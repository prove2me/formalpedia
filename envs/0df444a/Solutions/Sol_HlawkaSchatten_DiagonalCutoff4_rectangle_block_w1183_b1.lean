-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1183_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:22.045531+00:00
-- url     : https://prove2.me/submissions/818aad55-5302-482f-b090-8b9b2d393e78

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
theorem support_rectangle_w1183_s3_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144056901/10000000000 : ℝ)*x 0 + (678135027/1250000000 : ℝ)*x 1 + (5235796841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144056901/10000000000 : ℝ)^1047 ≤ (13025577364587/100000000000000 : ℝ)^791 := by
    have hnat : (2144056901 : ℕ)^1047*100000000000000^791 ≤ 13025577364587^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144056901 10000000000 13025577364587 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678135027/1250000000 : ℝ)^1047 ≤ (2225456574139/5000000000000 : ℝ)^791 := by
    have hnat : (678135027 : ℕ)^1047*5000000000000^791 ≤ 2225456574139^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678135027 1250000000 2225456574139 5000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235796841/10000000000 : ℝ)^1047 ≤ (331760086961/781250000000 : ℝ)^791 := by
    have hnat : (5235796841 : ℕ)^1047*781250000000^791 ≤ 331760086961^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235796841 10000000000 331760086961 781250000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144056901/10000000000 : ℝ), (678135027/1250000000 : ℝ), (5235796841/10000000000 : ℝ)] ![(13025577364587/100000000000000 : ℝ), (2225456574139/5000000000000 : ℝ), (331760086961/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144056901/10000000000 : ℝ)|^1047 ≤ (13025577364587/100000000000000 : ℝ)^791
        have hw : |(-2144056901/10000000000 : ℝ)|=(2144056901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678135027/1250000000 : ℝ)|^1047 ≤ (2225456574139/5000000000000 : ℝ)^791
        have hw : |(678135027/1250000000 : ℝ)|=(678135027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235796841/10000000000 : ℝ)|^1047 ≤ (331760086961/781250000000 : ℝ)^791
        have hw : |(5235796841/10000000000 : ℝ)|=(5235796841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s3_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5352823357/10000000000 : ℝ)*x 0 + (-560182011/2500000000 : ℝ)*x 1 + (5235796647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352823357/10000000000 : ℝ)^1047 ≤ (1366442138669/3125000000000 : ℝ)^791 := by
    have hnat : (5352823357 : ℕ)^1047*3125000000000^791 ≤ 1366442138669^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352823357 10000000000 1366442138669 3125000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560182011/2500000000 : ℝ)^1047 ≤ (3452140624197/25000000000000 : ℝ)^791 := by
    have hnat : (560182011 : ℕ)^1047*25000000000000^791 ≤ 3452140624197^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560182011 2500000000 3452140624197 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235796647/10000000000 : ℝ)^1047 ≤ (1698611561933/4000000000000 : ℝ)^791 := by
    have hnat : (5235796647 : ℕ)^1047*4000000000000^791 ≤ 1698611561933^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235796647 10000000000 1698611561933 4000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352823357/10000000000 : ℝ), (-560182011/2500000000 : ℝ), (5235796647/10000000000 : ℝ)] ![(1366442138669/3125000000000 : ℝ), (3452140624197/25000000000000 : ℝ), (1698611561933/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352823357/10000000000 : ℝ)|^1047 ≤ (1366442138669/3125000000000 : ℝ)^791
        have hw : |(5352823357/10000000000 : ℝ)|=(5352823357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560182011/2500000000 : ℝ)|^1047 ≤ (3452140624197/25000000000000 : ℝ)^791
        have hw : |(-560182011/2500000000 : ℝ)|=(560182011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235796647/10000000000 : ℝ)|^1047 ≤ (1698611561933/4000000000000 : ℝ)^791
        have hw : |(5235796647/10000000000 : ℝ)|=(5235796647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s3_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1070564689/2000000000 : ℝ)*x 0 + (40904661/78125000 : ℝ)*x 1 + (-1120363989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070564689/2000000000 : ℝ)^1047 ≤ (43726149388913/100000000000000 : ℝ)^791 := by
    have hnat : (1070564689 : ℕ)^1047*100000000000000^791 ≤ 43726149388913^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070564689 2000000000 43726149388913 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40904661/78125000 : ℝ)^1047 ≤ (42465288629641/100000000000000 : ℝ)^791 := by
    have hnat : (40904661 : ℕ)^1047*100000000000000^791 ≤ 42465288629641^791*78125000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40904661 78125000 42465288629641 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120363989/5000000000 : ℝ)^1047 ≤ (13808561958427/100000000000000 : ℝ)^791 := by
    have hnat : (1120363989 : ℕ)^1047*100000000000000^791 ≤ 13808561958427^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120363989 5000000000 13808561958427 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070564689/2000000000 : ℝ), (40904661/78125000 : ℝ), (-1120363989/5000000000 : ℝ)] ![(43726149388913/100000000000000 : ℝ), (42465288629641/100000000000000 : ℝ), (13808561958427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070564689/2000000000 : ℝ)|^1047 ≤ (43726149388913/100000000000000 : ℝ)^791
        have hw : |(1070564689/2000000000 : ℝ)|=(1070564689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40904661/78125000 : ℝ)|^1047 ≤ (42465288629641/100000000000000 : ℝ)^791
        have hw : |(40904661/78125000 : ℝ)|=(40904661/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120363989/5000000000 : ℝ)|^1047 ≤ (13808561958427/100000000000000 : ℝ)^791
        have hw : |(-1120363989/5000000000 : ℝ)|=(1120363989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s3_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4356920221/10000000000 : ℝ)*x 0 + (2085593619/5000000000 : ℝ)*x 1 + (284424531/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356920221/10000000000 : ℝ)^1047 ≤ (8324216325817/25000000000000 : ℝ)^791 := by
    have hnat : (4356920221 : ℕ)^1047*25000000000000^791 ≤ 8324216325817^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356920221 10000000000 8324216325817 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085593619/5000000000 : ℝ)^1047 ≤ (31431142289507/100000000000000 : ℝ)^791 := by
    have hnat : (2085593619 : ℕ)^1047*100000000000000^791 ≤ 31431142289507^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085593619 5000000000 31431142289507 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284424531/625000000 : ℝ)^1047 ≤ (35271992398901/100000000000000 : ℝ)^791 := by
    have hnat : (284424531 : ℕ)^1047*100000000000000^791 ≤ 35271992398901^791*625000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284424531 625000000 35271992398901 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356920221/10000000000 : ℝ), (2085593619/5000000000 : ℝ), (284424531/625000000 : ℝ)] ![(8324216325817/25000000000000 : ℝ), (31431142289507/100000000000000 : ℝ), (35271992398901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356920221/10000000000 : ℝ)|^1047 ≤ (8324216325817/25000000000000 : ℝ)^791
        have hw : |(4356920221/10000000000 : ℝ)|=(4356920221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085593619/5000000000 : ℝ)|^1047 ≤ (31431142289507/100000000000000 : ℝ)^791
        have hw : |(2085593619/5000000000 : ℝ)|=(2085593619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(284424531/625000000 : ℝ)|^1047 ≤ (35271992398901/100000000000000 : ℝ)^791
        have hw : |(284424531/625000000 : ℝ)|=(284424531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s3_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144073109/10000000000 : ℝ)*x 0 + (523651111/1000000000 : ℝ)*x 1 + (5424362077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144073109/10000000000 : ℝ)^1047 ≤ (40705336561/312500000000 : ℝ)^791 := by
    have hnat : (2144073109 : ℕ)^1047*312500000000^791 ≤ 40705336561^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144073109 10000000000 40705336561 312500000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523651111/1000000000 : ℝ)^1047 ≤ (331819994701/781250000000 : ℝ)^791 := by
    have hnat : (523651111 : ℕ)^1047*781250000000^791 ≤ 331819994701^791*1000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523651111 1000000000 331819994701 781250000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424362077/10000000000 : ℝ)^1047 ≤ (22250666479837/50000000000000 : ℝ)^791 := by
    have hnat : (5424362077 : ℕ)^1047*50000000000000^791 ≤ 22250666479837^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424362077 10000000000 22250666479837 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144073109/10000000000 : ℝ), (523651111/1000000000 : ℝ), (5424362077/10000000000 : ℝ)] ![(40705336561/312500000000 : ℝ), (331819994701/781250000000 : ℝ), (22250666479837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144073109/10000000000 : ℝ)|^1047 ≤ (40705336561/312500000000 : ℝ)^791
        have hw : |(-2144073109/10000000000 : ℝ)|=(2144073109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523651111/1000000000 : ℝ)|^1047 ≤ (331819994701/781250000000 : ℝ)^791
        have hw : |(523651111/1000000000 : ℝ)|=(523651111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424362077/10000000000 : ℝ)|^1047 ≤ (22250666479837/50000000000000 : ℝ)^791
        have hw : |(5424362077/10000000000 : ℝ)|=(5424362077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s3_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (33154551/62500000 : ℝ)*x 0 + (-16417299/80000000 : ℝ)*x 1 + (1356090507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33154551/62500000 : ℝ)^1047 ≤ (8641374780099/20000000000000 : ℝ)^791 := by
    have hnat : (33154551 : ℕ)^1047*20000000000000^791 ≤ 8641374780099^791*62500000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33154551 62500000 8641374780099 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16417299/80000000 : ℝ)^1047 ≤ (1536474207961/12500000000000 : ℝ)^791 := by
    have hnat : (16417299 : ℕ)^1047*12500000000000^791 ≤ 1536474207961^791*80000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16417299 80000000 1536474207961 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356090507/2500000000 : ℝ)^1047 ≤ (44501332427577/100000000000000 : ℝ)^791 := by
    have hnat : (1356090507 : ℕ)^1047*100000000000000^791 ≤ 44501332427577^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356090507 2500000000 44501332427577 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33154551/62500000 : ℝ), (-16417299/80000000 : ℝ), (1356090507/2500000000 : ℝ)] ![(8641374780099/20000000000000 : ℝ), (1536474207961/12500000000000 : ℝ), (44501332427577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33154551/62500000 : ℝ)|^1047 ≤ (8641374780099/20000000000000 : ℝ)^791
        have hw : |(33154551/62500000 : ℝ)|=(33154551/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16417299/80000000 : ℝ)|^1047 ≤ (1536474207961/12500000000000 : ℝ)^791
        have hw : |(-16417299/80000000 : ℝ)|=(16417299/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356090507/2500000000 : ℝ)|^1047 ≤ (44501332427577/100000000000000 : ℝ)^791
        have hw : |(1356090507/2500000000 : ℝ)|=(1356090507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s3_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304727823/10000000000 : ℝ)*x 0 + (2712181199/5000000000 : ℝ)*x 1 + (-1026081163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304727823/10000000000 : ℝ)^1047 ≤ (4320687026729/10000000000000 : ℝ)^791 := by
    have hnat : (5304727823 : ℕ)^1047*10000000000000^791 ≤ 4320687026729^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304727823 10000000000 4320687026729 10000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712181199/5000000000 : ℝ)^1047 ≤ (44501336445451/100000000000000 : ℝ)^791 := by
    have hnat : (2712181199 : ℕ)^1047*100000000000000^791 ≤ 44501336445451^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712181199 5000000000 44501336445451 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026081163/5000000000 : ℝ)^1047 ≤ (12291793275207/100000000000000 : ℝ)^791 := by
    have hnat : (1026081163 : ℕ)^1047*100000000000000^791 ≤ 12291793275207^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026081163 5000000000 12291793275207 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304727823/10000000000 : ℝ), (2712181199/5000000000 : ℝ), (-1026081163/5000000000 : ℝ)] ![(4320687026729/10000000000000 : ℝ), (44501336445451/100000000000000 : ℝ), (12291793275207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304727823/10000000000 : ℝ)|^1047 ≤ (4320687026729/10000000000000 : ℝ)^791
        have hw : |(5304727823/10000000000 : ℝ)|=(5304727823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712181199/5000000000 : ℝ)|^1047 ≤ (44501336445451/100000000000000 : ℝ)^791
        have hw : |(2712181199/5000000000 : ℝ)|=(2712181199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026081163/5000000000 : ℝ)|^1047 ≤ (12291793275207/100000000000000 : ℝ)^791
        have hw : |(-1026081163/5000000000 : ℝ)|=(1026081163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s3_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4356953003/10000000000 : ℝ)*x 0 + (4549359687/10000000000 : ℝ)*x 1 + (4172627609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356953003/10000000000 : ℝ)^1047 ≤ (33297196915021/100000000000000 : ℝ)^791 := by
    have hnat : (4356953003 : ℕ)^1047*100000000000000^791 ≤ 33297196915021^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356953003 10000000000 33297196915021 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4549359687/10000000000 : ℝ)^1047 ≤ (7051458737053/20000000000000 : ℝ)^791 := by
    have hnat : (4549359687 : ℕ)^1047*20000000000000^791 ≤ 7051458737053^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549359687 10000000000 7051458737053 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172627609/10000000000 : ℝ)^1047 ≤ (7861377349009/25000000000000 : ℝ)^791 := by
    have hnat : (4172627609 : ℕ)^1047*25000000000000^791 ≤ 7861377349009^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172627609 10000000000 7861377349009 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356953003/10000000000 : ℝ), (4549359687/10000000000 : ℝ), (4172627609/10000000000 : ℝ)] ![(33297196915021/100000000000000 : ℝ), (7051458737053/20000000000000 : ℝ), (7861377349009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356953003/10000000000 : ℝ)|^1047 ≤ (33297196915021/100000000000000 : ℝ)^791
        have hw : |(4356953003/10000000000 : ℝ)|=(4356953003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4549359687/10000000000 : ℝ)|^1047 ≤ (7051458737053/20000000000000 : ℝ)^791
        have hw : |(4549359687/10000000000 : ℝ)|=(4549359687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172627609/10000000000 : ℝ)|^1047 ≤ (7861377349009/25000000000000 : ℝ)^791
        have hw : |(4172627609/10000000000 : ℝ)|=(4172627609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2313/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10753/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2313/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2313/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2313/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2313/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2313/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2313/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2313/25000 : ℝ) ^ (8375/2048 : ℝ) ≤ (5923385474329/100000000000000000 : ℝ) := by
    have hpowers : (2313/25000 : ℝ)^8375 ≤ (5923385474329/100000000000000000 : ℝ)^2048 := by
      have hnat : (2313 : ℕ)^8375*100000000000000000^2048 ≤ 5923385474329^2048*25000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2313 25000 5923385474329 100000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2313/25000 : ℝ)) (X := (5923385474329/100000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16383/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (15322001146110587/25000000000000000000 : ℝ) := by
    have hpowers : (16383/100000 : ℝ)^8375 ≤ (15322001146110587/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16383 : ℕ)^8375*25000000000000000000^2048 ≤ 15322001146110587^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16383 100000 15322001146110587 25000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16383/100000 : ℝ)) (X := (15322001146110587/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005923385474329/50000000000000000 : ℝ) ≤ (1250036210598911/1250000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50005923385474329/50000000000000000 : ℝ)^2048 ≤ (1250036210598911/1250000000000000 : ℝ)^8375 := by
      have hnat : (50005923385474329 : ℕ)^2048*1250000000000000^8375 ≤ 1250036210598911^8375*50000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005923385474329 50000000000000000 1250036210598911 1250000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250036210598911/1250000000000000 : ℝ)) (X := (50005923385474329/50000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25016802847514692837/25000000000000000000 : ℝ) ≤ (10001643152172857/10000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (25016802847514692837/25000000000000000000 : ℝ)^2048 ≤ (10001643152172857/10000000000000000 : ℝ)^8375 := by
      have hnat : (25016802847514692837 : ℕ)^2048*10000000000000000^8375 ≤ 10001643152172857^8375*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016802847514692837 25000000000000000000 10001643152172857 10000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001643152172857/10000000000000000 : ℝ)) (X := (25016802847514692837/25000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515322001146110587/12500000000000000000 : ℝ) ≤ (5001498309777213/5000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (12515322001146110587/12500000000000000000 : ℝ)^2048 ≤ (5001498309777213/5000000000000000 : ℝ)^8375 := by
      have hnat : (12515322001146110587 : ℕ)^2048*5000000000000000^8375 ≤ 5001498309777213^8375*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515322001146110587 12500000000000000000 5001498309777213 5000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001498309777213/5000000000000000 : ℝ)) (X := (12515322001146110587/12500000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5923385474329/100000000000000000 : ℝ) ≤ ((742573137310605437/742812500000000000 : ℝ)+2*(1353467381569/713100000000000 : ℝ)*(2313/25000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (742573137310605437/742812500000000000 : ℝ)+2*(1353467381569/713100000000000 : ℝ)*(2313/25000 : ℝ)=(1250036210598911/1250000000000000 : ℝ) by norm_num, show 1+2*(5923385474329/100000000000000000 : ℝ)=(50005923385474329/50000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15322001146110587/25000000000000000000 : ℝ)+(5923385474329/100000000000000000 : ℝ) ≤ ((742573137310605437/742812500000000000 : ℝ)+(1353467381569/713100000000000 : ℝ)*((16383/100000 : ℝ)+(2313/25000 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (742573137310605437/742812500000000000 : ℝ)+(1353467381569/713100000000000 : ℝ)*((16383/100000 : ℝ)+(2313/25000 : ℝ))=(10001643152172857/10000000000000000 : ℝ) by norm_num, show 1+(15322001146110587/25000000000000000000 : ℝ)+(5923385474329/100000000000000000 : ℝ)=(25016802847514692837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15322001146110587/25000000000000000000 : ℝ) ≤ ((742573137310605437/742812500000000000 : ℝ)+2*(1353467381569/713100000000000 : ℝ)*(16383/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (742573137310605437/742812500000000000 : ℝ)+2*(1353467381569/713100000000000 : ℝ)*(16383/100000 : ℝ)=(5001498309777213/5000000000000000 : ℝ) by norm_num, show 1+2*(15322001146110587/25000000000000000000 : ℝ)=(12515322001146110587/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (742573137310605437/742812500000000000 : ℝ)*(X 1 0+X 2 0)+(1353467381569/713100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (2313/25000 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (742573137310605437/742812500000000000 : ℝ)) (alpha := (1353467381569/713100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (742573137310605437/742812500000000000 : ℝ)*(X 0 1+X 2 1)+(1353467381569/713100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (2313/25000 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (742573137310605437/742812500000000000 : ℝ)) (alpha := (1353467381569/713100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (742573137310605437/742812500000000000 : ℝ)*(X 0 2+X 1 2)+(1353467381569/713100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (2313/25000 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (742573137310605437/742812500000000000 : ℝ)) (alpha := (1353467381569/713100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2144056901/10000000000 : ℝ)*X 0 0+(678135027/1250000000 : ℝ)*X 0 1+(5235796841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352823357/10000000000 : ℝ)*X 1 0+(-560182011/2500000000 : ℝ)*X 1 1+(5235796647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070564689/2000000000 : ℝ)*X 2 0+(40904661/78125000 : ℝ)*X 2 1+(-1120363989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356920221/10000000000 : ℝ)*X 0 0+(2085593619/5000000000 : ℝ)*X 0 1+(284424531/625000000 : ℝ)*X 0 2+(4356920221/10000000000 : ℝ)*X 1 0+(2085593619/5000000000 : ℝ)*X 1 1+(284424531/625000000 : ℝ)*X 1 2+(4356920221/10000000000 : ℝ)*X 2 0+(2085593619/5000000000 : ℝ)*X 2 1+(284424531/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144073109/10000000000 : ℝ)*X 0 0+(523651111/1000000000 : ℝ)*X 0 1+(5424362077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33154551/62500000 : ℝ)*X 1 0+(-16417299/80000000 : ℝ)*X 1 1+(1356090507/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304727823/10000000000 : ℝ)*X 2 0+(2712181199/5000000000 : ℝ)*X 2 1+(-1026081163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356953003/10000000000 : ℝ)*X 0 0+(4549359687/10000000000 : ℝ)*X 0 1+(4172627609/10000000000 : ℝ)*X 0 2+(4356953003/10000000000 : ℝ)*X 1 0+(4549359687/10000000000 : ℝ)*X 1 1+(4172627609/10000000000 : ℝ)*X 1 2+(4356953003/10000000000 : ℝ)*X 2 0+(4549359687/10000000000 : ℝ)*X 2 1+(4172627609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2321734087707278333066859/290161132812500000000000000000 : ℝ) := by norm_num
    linear_combination (369660281/20000000000000 : ℝ)*(base19) + (359372729/20000000000000 : ℝ)*(base23) + (9253173/12500000000000 : ℝ)*(lower2) + (23650553/12500000000000 : ℝ)*(upper3) + (85681489/50000000000000 : ℝ)*(upper5) + (1979372982172391/50000000000000 : ℝ)*(major0) + (1979372982172391/50000000000000 : ℝ)*(major1) + (1979372982172391/50000000000000 : ℝ)*(major2) + (5283113710939459/100000000000000 : ℝ)*(sp0) + (2641571545833961/50000000000000 : ℝ)*(sp1) + (2641571571552841/50000000000000 : ℝ)*(sp2) + (1317165243650349/50000000000000 : ℝ)*(sp3) + (7807257467/25000000000000 : ℝ)*(sp4) + (8117350873/50000000000000 : ℝ)*(sp7) + (658586680500611/25000000000000 : ℝ)*(f.failure) + (5283144939969327/100000000000000 : ℝ)*(f.sum) + (34504695519917/35655000000000000000000000000 : ℝ)*base66 + (38805286757786363/55710937500000000000000000000000 : ℝ)*base67 + (186186300791255399/111421875000000000000000000000000 : ℝ)*base70 + (17676099581276137/55710937500000000000000000000000 : ℝ)*base72 + (1977451199999/1114218750000000000000000000 : ℝ)*base73 + (202289082596052131/27855468750000000000000000000000 : ℝ)*base76 + (3918859393901137/55710937500000000000000000000000 : ℝ)*base78 + (133366244740661363/55710937500000000000000000000000 : ℝ)*base79 + (26520606872107/8913750000000000000000000000 : ℝ)*base81 + (3018849/500000000000000000000 : ℝ)*base89 + (3018849/500000000000000000000 : ℝ)*base91 + (3018849/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177646489033159437644293349/37140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (757909827/50000000000000 : ℝ)*(base19) + (178844661/12500000000000 : ℝ)*(base23) + (92948909/100000000000000 : ℝ)*(upper3) + (124698781/100000000000000 : ℝ)*(lower4) + (18869489/10000000000000 : ℝ)*(upper5) + (3988885376434783/100000000000000 : ℝ)*(major0) + (3988885376434783/100000000000000 : ℝ)*(major1) + (3988885376434783/100000000000000 : ℝ)*(major2) + (15234789773/50000000000000 : ℝ)*(sp1) + (32460216039/100000000000000 : ℝ)*(sp2) + (5323367605594117/100000000000000 : ℝ)*(sp4) + (5323335620194917/100000000000000 : ℝ)*(sp5) + (532333371462079/10000000000000 : ℝ)*(sp6) + (1327201493919763/50000000000000 : ℝ)*(sp7) + (1327201493919763/50000000000000 : ℝ)*(f.failure) + (5323367605594117/100000000000000 : ℝ)*(f.sum) + (17108303411303/2228437500000000000000000000 : ℝ)*base66 + (52278632433823097/55710937500000000000000000000000 : ℝ)*base67 + (367920013031068069/111421875000000000000000000000000 : ℝ)*base69 + (670224648905458153/55710937500000000000000000000000 : ℝ)*base72 + (17519437676869/17827500000000000000000000000 : ℝ)*base74 + (803972994978823097/55710937500000000000000000000000 : ℝ)*base75 + (81911563100443069/111421875000000000000000000000000 : ℝ)*base77 + (32807339329304059/6963867187500000000000000000000 : ℝ)*base79 + (104855793312533/35655000000000000000000000000 : ℝ)*base82 + (4278417/1000000000000000000000 : ℝ)*base89 + (4278417/1000000000000000000000 : ℝ)*base91 + (4278417/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1183_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2313/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10753/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1183_s4_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073372769/5000000000 : ℝ)*x 0 + (5399995567/10000000000 : ℝ)*x 1 + (262956067/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073372769/5000000000 : ℝ)^1047 ≤ (13047202116761/100000000000000 : ℝ)^791 := by
    have hnat : (1073372769 : ℕ)^1047*100000000000000^791 ≤ 13047202116761^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073372769 5000000000 13047202116761 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399995567/10000000000 : ℝ)^1047 ≤ (8847385337857/20000000000000 : ℝ)^791 := by
    have hnat : (5399995567 : ℕ)^1047*20000000000000^791 ≤ 8847385337857^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399995567 10000000000 8847385337857 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262956067/500000000 : ℝ)^1047 ≤ (10678967794907/25000000000000 : ℝ)^791 := by
    have hnat : (262956067 : ℕ)^1047*25000000000000^791 ≤ 10678967794907^791*500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262956067 500000000 10678967794907 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073372769/5000000000 : ℝ), (5399995567/10000000000 : ℝ), (262956067/500000000 : ℝ)] ![(13047202116761/100000000000000 : ℝ), (8847385337857/20000000000000 : ℝ), (10678967794907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073372769/5000000000 : ℝ)|^1047 ≤ (13047202116761/100000000000000 : ℝ)^791
        have hw : |(-1073372769/5000000000 : ℝ)|=(1073372769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399995567/10000000000 : ℝ)|^1047 ≤ (8847385337857/20000000000000 : ℝ)^791
        have hw : |(5399995567/10000000000 : ℝ)|=(5399995567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262956067/500000000 : ℝ)|^1047 ≤ (10678967794907/25000000000000 : ℝ)^791
        have hw : |(262956067/500000000 : ℝ)|=(262956067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s4_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069306703/2000000000 : ℝ)*x 0 + (-443661431/2000000000 : ℝ)*x 1 + (5259121733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069306703/2000000000 : ℝ)^1047 ≤ (43658152081647/100000000000000 : ℝ)^791 := by
    have hnat : (1069306703 : ℕ)^1047*100000000000000^791 ≤ 43658152081647^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069306703 2000000000 43658152081647 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443661431/2000000000 : ℝ)^1047 ≤ (13625972501577/100000000000000 : ℝ)^791 := by
    have hnat : (443661431 : ℕ)^1047*100000000000000^791 ≤ 13625972501577^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443661431 2000000000 13625972501577 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259121733/10000000000 : ℝ)^1047 ≤ (21357937702373/50000000000000 : ℝ)^791 := by
    have hnat : (5259121733 : ℕ)^1047*50000000000000^791 ≤ 21357937702373^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259121733 10000000000 21357937702373 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069306703/2000000000 : ℝ), (-443661431/2000000000 : ℝ), (5259121733/10000000000 : ℝ)] ![(43658152081647/100000000000000 : ℝ), (13625972501577/100000000000000 : ℝ), (21357937702373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069306703/2000000000 : ℝ)|^1047 ≤ (43658152081647/100000000000000 : ℝ)^791
        have hw : |(1069306703/2000000000 : ℝ)|=(1069306703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443661431/2000000000 : ℝ)|^1047 ≤ (13625972501577/100000000000000 : ℝ)^791
        have hw : |(-443661431/2000000000 : ℝ)|=(443661431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259121733/10000000000 : ℝ)|^1047 ≤ (21357937702373/50000000000000 : ℝ)^791
        have hw : |(5259121733/10000000000 : ℝ)|=(5259121733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s4_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346533417/10000000000 : ℝ)*x 0 + (5259122397/10000000000 : ℝ)*x 1 + (-2218306407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346533417/10000000000 : ℝ)^1047 ≤ (43658151022419/100000000000000 : ℝ)^791 := by
    have hnat : (5346533417 : ℕ)^1047*100000000000000^791 ≤ 43658151022419^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346533417 10000000000 43658151022419 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259122397/10000000000 : ℝ)^1047 ≤ (5339485317921/12500000000000 : ℝ)^791 := by
    have hnat : (5259122397 : ℕ)^1047*12500000000000^791 ≤ 5339485317921^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259122397 10000000000 5339485317921 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218306407/10000000000 : ℝ)^1047 ≤ (13625966419981/100000000000000 : ℝ)^791 := by
    have hnat : (2218306407 : ℕ)^1047*100000000000000^791 ≤ 13625966419981^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218306407 10000000000 13625966419981 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346533417/10000000000 : ℝ), (5259122397/10000000000 : ℝ), (-2218306407/10000000000 : ℝ)] ![(43658151022419/100000000000000 : ℝ), (5339485317921/12500000000000 : ℝ), (13625966419981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346533417/10000000000 : ℝ)|^1047 ≤ (43658151022419/100000000000000 : ℝ)^791
        have hw : |(5346533417/10000000000 : ℝ)|=(5346533417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259122397/10000000000 : ℝ)|^1047 ≤ (5339485317921/12500000000000 : ℝ)^791
        have hw : |(5259122397/10000000000 : ℝ)|=(5259122397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2218306407/10000000000 : ℝ)|^1047 ≤ (13625966419981/100000000000000 : ℝ)^791
        have hw : |(-2218306407/10000000000 : ℝ)|=(2218306407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s4_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4358528233/10000000000 : ℝ)*x 0 + (4219522267/10000000000 : ℝ)*x 1 + (4502042767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358528233/10000000000 : ℝ)^1047 ≤ (33313132366681/100000000000000 : ℝ)^791 := by
    have hnat : (4358528233 : ℕ)^1047*100000000000000^791 ≤ 33313132366681^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358528233 10000000000 33313132366681 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219522267/10000000000 : ℝ)^1047 ≤ (15957069488503/50000000000000 : ℝ)^791 := by
    have hnat : (4219522267 : ℕ)^1047*50000000000000^791 ≤ 15957069488503^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219522267 10000000000 15957069488503 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502042767/10000000000 : ℝ)^1047 ≤ (34772728642993/100000000000000 : ℝ)^791 := by
    have hnat : (4502042767 : ℕ)^1047*100000000000000^791 ≤ 34772728642993^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502042767 10000000000 34772728642993 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358528233/10000000000 : ℝ), (4219522267/10000000000 : ℝ), (4502042767/10000000000 : ℝ)] ![(33313132366681/100000000000000 : ℝ), (15957069488503/50000000000000 : ℝ), (34772728642993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358528233/10000000000 : ℝ)|^1047 ≤ (33313132366681/100000000000000 : ℝ)^791
        have hw : |(4358528233/10000000000 : ℝ)|=(4358528233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4219522267/10000000000 : ℝ)|^1047 ≤ (15957069488503/50000000000000 : ℝ)^791
        have hw : |(4219522267/10000000000 : ℝ)|=(4219522267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502042767/10000000000 : ℝ)|^1047 ≤ (34772728642993/100000000000000 : ℝ)^791
        have hw : |(4502042767/10000000000 : ℝ)|=(4502042767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s4_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-536687973/2500000000 : ℝ)*x 0 + (1314879593/2500000000 : ℝ)*x 1 + (5399597193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536687973/2500000000 : ℝ)^1047 ≤ (3261813308119/25000000000000 : ℝ)^791 := by
    have hnat : (536687973 : ℕ)^1047*25000000000000^791 ≤ 3261813308119^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536687973 2500000000 3261813308119 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314879593/2500000000 : ℝ)^1047 ≤ (21360069848691/50000000000000 : ℝ)^791 := by
    have hnat : (1314879593 : ℕ)^1047*50000000000000^791 ≤ 21360069848691^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314879593 2500000000 21360069848691 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399597193/10000000000 : ℝ)^1047 ≤ (11058151762347/25000000000000 : ℝ)^791 := by
    have hnat : (5399597193 : ℕ)^1047*25000000000000^791 ≤ 11058151762347^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399597193 10000000000 11058151762347 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536687973/2500000000 : ℝ), (1314879593/2500000000 : ℝ), (5399597193/10000000000 : ℝ)] ![(3261813308119/25000000000000 : ℝ), (21360069848691/50000000000000 : ℝ), (11058151762347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536687973/2500000000 : ℝ)|^1047 ≤ (3261813308119/25000000000000 : ℝ)^791
        have hw : |(-536687973/2500000000 : ℝ)|=(536687973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314879593/2500000000 : ℝ)|^1047 ≤ (21360069848691/50000000000000 : ℝ)^791
        have hw : |(1314879593/2500000000 : ℝ)|=(1314879593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399597193/10000000000 : ℝ)|^1047 ≤ (11058151762347/25000000000000 : ℝ)^791
        have hw : |(5399597193/10000000000 : ℝ)|=(5399597193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s4_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5310738323/10000000000 : ℝ)*x 0 + (-1038915739/5000000000 : ℝ)*x 1 + (337474811/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310738323/10000000000 : ℝ)^1047 ≤ (43271681473313/100000000000000 : ℝ)^791 := by
    have hnat : (5310738323 : ℕ)^1047*100000000000000^791 ≤ 43271681473313^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310738323 10000000000 43271681473313 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038915739/5000000000 : ℝ)^1047 ≤ (12495713811957/100000000000000 : ℝ)^791 := by
    have hnat : (1038915739 : ℕ)^1047*100000000000000^791 ≤ 12495713811957^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038915739 5000000000 12495713811957 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337474811/625000000 : ℝ)^1047 ≤ (44232604696447/100000000000000 : ℝ)^791 := by
    have hnat : (337474811 : ℕ)^1047*100000000000000^791 ≤ 44232604696447^791*625000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337474811 625000000 44232604696447 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310738323/10000000000 : ℝ), (-1038915739/5000000000 : ℝ), (337474811/625000000 : ℝ)] ![(43271681473313/100000000000000 : ℝ), (12495713811957/100000000000000 : ℝ), (44232604696447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310738323/10000000000 : ℝ)|^1047 ≤ (43271681473313/100000000000000 : ℝ)^791
        have hw : |(5310738323/10000000000 : ℝ)|=(5310738323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1038915739/5000000000 : ℝ)|^1047 ≤ (12495713811957/100000000000000 : ℝ)^791
        have hw : |(-1038915739/5000000000 : ℝ)|=(1038915739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337474811/625000000 : ℝ)|^1047 ≤ (44232604696447/100000000000000 : ℝ)^791
        have hw : |(337474811/625000000 : ℝ)|=(337474811/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s4_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5310737509/10000000000 : ℝ)*x 0 + (1349899491/2500000000 : ℝ)*x 1 + (-415566247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310737509/10000000000 : ℝ)^1047 ≤ (8654334538869/20000000000000 : ℝ)^791 := by
    have hnat : (5310737509 : ℕ)^1047*20000000000000^791 ≤ 8654334538869^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310737509 10000000000 8654334538869 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349899491/2500000000 : ℝ)^1047 ≤ (44232615409379/100000000000000 : ℝ)^791 := by
    have hnat : (1349899491 : ℕ)^1047*100000000000000^791 ≤ 44232615409379^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349899491 2500000000 44232615409379 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415566247/2000000000 : ℝ)^1047 ≤ (6247855938821/50000000000000 : ℝ)^791 := by
    have hnat : (415566247 : ℕ)^1047*50000000000000^791 ≤ 6247855938821^791*2000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415566247 2000000000 6247855938821 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310737509/10000000000 : ℝ), (1349899491/2500000000 : ℝ), (-415566247/2000000000 : ℝ)] ![(8654334538869/20000000000000 : ℝ), (44232615409379/100000000000000 : ℝ), (6247855938821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310737509/10000000000 : ℝ)|^1047 ≤ (8654334538869/20000000000000 : ℝ)^791
        have hw : |(5310737509/10000000000 : ℝ)|=(5310737509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349899491/2500000000 : ℝ)|^1047 ≤ (44232615409379/100000000000000 : ℝ)^791
        have hw : |(1349899491/2500000000 : ℝ)|=(1349899491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415566247/2000000000 : ℝ)|^1047 ≤ (6247855938821/50000000000000 : ℝ)^791
        have hw : |(-415566247/2000000000 : ℝ)|=(415566247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s4_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (272408813/625000000 : ℝ)*x 0 + (4501248413/10000000000 : ℝ)*x 1 + (4220320501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272408813/625000000 : ℝ)^1047 ≤ (2082078850603/6250000000000 : ℝ)^791 := by
    have hnat : (272408813 : ℕ)^1047*6250000000000^791 ≤ 2082078850603^791*625000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272408813 625000000 2082078850603 6250000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501248413/10000000000 : ℝ)^1047 ≤ (34764607801393/100000000000000 : ℝ)^791 := by
    have hnat : (4501248413 : ℕ)^1047*100000000000000^791 ≤ 34764607801393^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501248413 10000000000 34764607801393 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4220320501/10000000000 : ℝ)^1047 ≤ (7980532643447/25000000000000 : ℝ)^791 := by
    have hnat : (4220320501 : ℕ)^1047*25000000000000^791 ≤ 7980532643447^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220320501 10000000000 7980532643447 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272408813/625000000 : ℝ), (4501248413/10000000000 : ℝ), (4220320501/10000000000 : ℝ)] ![(2082078850603/6250000000000 : ℝ), (34764607801393/100000000000000 : ℝ), (7980532643447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272408813/625000000 : ℝ)|^1047 ≤ (2082078850603/6250000000000 : ℝ)^791
        have hw : |(272408813/625000000 : ℝ)|=(272408813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501248413/10000000000 : ℝ)|^1047 ≤ (34764607801393/100000000000000 : ℝ)^791
        have hw : |(4501248413/10000000000 : ℝ)|=(4501248413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4220320501/10000000000 : ℝ)|^1047 ≤ (7980532643447/25000000000000 : ℝ)^791
        have hw : |(4220320501/10000000000 : ℝ)|=(4220320501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10753/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11251/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10753/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10753/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10753/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10753/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10753/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10753/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10753/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (1095419482426859/10000000000000000000 : ℝ) := by
    have hpowers : (10753/100000 : ℝ)^8375 ≤ (1095419482426859/10000000000000000000 : ℝ)^2048 := by
      have hnat : (10753 : ℕ)^8375*10000000000000000000^2048 ≤ 1095419482426859^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10753 100000 1095419482426859 10000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10753/100000 : ℝ)) (X := (1095419482426859/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (19996244024655631/50000000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^8375 ≤ (19996244024655631/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14759 : ℕ)^8375*50000000000000000000^2048 ≤ 19996244024655631^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 19996244024655631 50000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (19996244024655631/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001095419482426859/5000000000000000000 : ℝ) ≤ (625033481096567/625000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (5001095419482426859/5000000000000000000 : ℝ)^2048 ≤ (625033481096567/625000000000000 : ℝ)^8375 := by
      have hnat : (5001095419482426859 : ℕ)^2048*625000000000000^8375 ≤ 625033481096567^8375*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001095419482426859 5000000000000000000 625033481096567 625000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033481096567/625000000000000 : ℝ)) (X := (5001095419482426859/5000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012736670718394963/25000000000000000000 : ℝ) ≤ (2500311399204129/2500000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (25012736670718394963/25000000000000000000 : ℝ)^2048 ≤ (2500311399204129/2500000000000000 : ℝ)^8375 := by
      have hnat : (25012736670718394963 : ℕ)^2048*2500000000000000^8375 ≤ 2500311399204129^8375*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012736670718394963 25000000000000000000 2500311399204129 2500000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500311399204129/2500000000000000 : ℝ)) (X := (25012736670718394963/25000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019996244024655631/25000000000000000000 : ℝ) ≤ (250048887402199/250000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (25019996244024655631/25000000000000000000 : ℝ)^2048 ≤ (250048887402199/250000000000000 : ℝ)^8375 := by
      have hnat : (25019996244024655631 : ℕ)^2048*250000000000000^8375 ≤ 250048887402199^8375*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019996244024655631 25000000000000000000 250048887402199 250000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250048887402199/250000000000000 : ℝ)) (X := (25019996244024655631/25000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1095419482426859/10000000000000000000 : ℝ) ≤ ((5005859863829235471/5007500000000000000 : ℝ)+2*(177474817861/100150000000000 : ℝ)*(10753/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (5005859863829235471/5007500000000000000 : ℝ)+2*(177474817861/100150000000000 : ℝ)*(10753/100000 : ℝ)=(625033481096567/625000000000000 : ℝ) by norm_num, show 1+2*(1095419482426859/10000000000000000000 : ℝ)=(5001095419482426859/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19996244024655631/50000000000000000000 : ℝ)+(1095419482426859/10000000000000000000 : ℝ) ≤ ((5005859863829235471/5007500000000000000 : ℝ)+(177474817861/100150000000000 : ℝ)*((14759/100000 : ℝ)+(10753/100000 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (5005859863829235471/5007500000000000000 : ℝ)+(177474817861/100150000000000 : ℝ)*((14759/100000 : ℝ)+(10753/100000 : ℝ))=(2500311399204129/2500000000000000 : ℝ) by norm_num, show 1+(19996244024655631/50000000000000000000 : ℝ)+(1095419482426859/10000000000000000000 : ℝ)=(25012736670718394963/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19996244024655631/50000000000000000000 : ℝ) ≤ ((5005859863829235471/5007500000000000000 : ℝ)+2*(177474817861/100150000000000 : ℝ)*(14759/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (5005859863829235471/5007500000000000000 : ℝ)+2*(177474817861/100150000000000 : ℝ)*(14759/100000 : ℝ)=(250048887402199/250000000000000 : ℝ) by norm_num, show 1+2*(19996244024655631/50000000000000000000 : ℝ)=(25019996244024655631/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5005859863829235471/5007500000000000000 : ℝ)*(X 1 0+X 2 0)+(177474817861/100150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (10753/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (5005859863829235471/5007500000000000000 : ℝ)) (alpha := (177474817861/100150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5005859863829235471/5007500000000000000 : ℝ)*(X 0 1+X 2 1)+(177474817861/100150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (10753/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (5005859863829235471/5007500000000000000 : ℝ)) (alpha := (177474817861/100150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5005859863829235471/5007500000000000000 : ℝ)*(X 0 2+X 1 2)+(177474817861/100150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (10753/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (5005859863829235471/5007500000000000000 : ℝ)) (alpha := (177474817861/100150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1073372769/5000000000 : ℝ)*X 0 0+(5399995567/10000000000 : ℝ)*X 0 1+(262956067/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069306703/2000000000 : ℝ)*X 1 0+(-443661431/2000000000 : ℝ)*X 1 1+(5259121733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346533417/10000000000 : ℝ)*X 2 0+(5259122397/10000000000 : ℝ)*X 2 1+(-2218306407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358528233/10000000000 : ℝ)*X 0 0+(4219522267/10000000000 : ℝ)*X 0 1+(4502042767/10000000000 : ℝ)*X 0 2+(4358528233/10000000000 : ℝ)*X 1 0+(4219522267/10000000000 : ℝ)*X 1 1+(4502042767/10000000000 : ℝ)*X 1 2+(4358528233/10000000000 : ℝ)*X 2 0+(4219522267/10000000000 : ℝ)*X 2 1+(4502042767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-536687973/2500000000 : ℝ)*X 0 0+(1314879593/2500000000 : ℝ)*X 0 1+(5399597193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310738323/10000000000 : ℝ)*X 1 0+(-1038915739/5000000000 : ℝ)*X 1 1+(337474811/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310737509/10000000000 : ℝ)*X 2 0+(1349899491/2500000000 : ℝ)*X 2 1+(-415566247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272408813/625000000 : ℝ)*X 0 0+(4501248413/10000000000 : ℝ)*X 0 1+(4220320501/10000000000 : ℝ)*X 0 2+(272408813/625000000 : ℝ)*X 1 0+(4501248413/10000000000 : ℝ)*X 1 1+(4220320501/10000000000 : ℝ)*X 1 2+(272408813/625000000 : ℝ)*X 2 0+(4501248413/10000000000 : ℝ)*X 2 1+(4220320501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (159690140443850844288738537/31296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69026041/5000000000000 : ℝ)*(base19) + (945016917/100000000000000 : ℝ)*(base23) + (7253989/4000000000000 : ℝ)*(lower2) + (338395081/50000000000000 : ℝ)*(upper5) + (332445298212631/6250000000000 : ℝ)*(major0) + (332445298212631/6250000000000 : ℝ)*(major1) + (332445298212631/6250000000000 : ℝ)*(major2) + (7098567342497167/100000000000000 : ℝ)*(sp0) + (7098632412137859/100000000000000 : ℝ)*(sp1) + (7098637896575747/100000000000000 : ℝ)*(sp2) + (3539593841748219/100000000000000 : ℝ)*(sp3) + (35749547749/50000000000000 : ℝ)*(sp4) + (1009786797/20000000000000 : ℝ)*(sp5) + (16689382269/100000000000000 : ℝ)*(sp7) + (442451316391311/12500000000000 : ℝ)*(f.failure) + (887329855199083/12500000000000 : ℝ)*(f.sum) + (42915198886557/10015000000000000000000000000 : ℝ)*base65 + (31439146056236339/1956054687500000000000000000000 : ℝ)*base68 + (571664456155453299/31296875000000000000000000000000 : ℝ)*base70 + (6368836725789019/7824218750000000000000000000000 : ℝ)*base71 + (1221357014387/10015000000000000000000000000 : ℝ)*base73 + (470321643236625087/15648437500000000000000000000000 : ℝ)*base76 + (313369219907422049/31296875000000000000000000000000 : ℝ)*base78 + (330242923925218837/15648437500000000000000000000000 : ℝ)*base80 + (29081613627617/10015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (930149/250000000000000000000 : ℝ)*base89 + (930149/250000000000000000000 : ℝ)*base91 + (930149/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52311450212395344756423/10015000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24980699/10000000000000 : ℝ)*(base19) + (94867677/100000000000000 : ℝ)*(upper2) + (28934987/10000000000000 : ℝ)*(lower4) + (191017427/100000000000000 : ℝ)*(upper5) + (2674621496356813/50000000000000 : ℝ)*(major0) + (2674621496356813/50000000000000 : ℝ)*(major1) + (2674621496356813/50000000000000 : ℝ)*(major2) + (2846851957/100000000000000 : ℝ)*(sp0) + (17939903503/100000000000000 : ℝ)*(sp2) + (3999397567/25000000000000 : ℝ)*(sp3) + (3569415134448367/50000000000000 : ℝ)*(sp4) + (7138832865941701/100000000000000 : ℝ)*(sp5) + (1784703793961297/25000000000000 : ℝ)*(sp6) + (3559636697977943/100000000000000 : ℝ)*(sp7) + (889913173892053/25000000000000 : ℝ)*(f.failure) + (1784708278937173/25000000000000 : ℝ)*(f.sum) + (201251830978969/5007500000000000000000000000 : ℝ)*base66 + (3448829303081013923/250375000000000000000000000000000 : ℝ)*base67 + (696930798071388923/250375000000000000000000000000000 : ℝ)*base69 + (307423319192361077/250375000000000000000000000000000 : ℝ)*base72 + (3606247441083/10015000000000000000000000000 : ℝ)*base74 + (84030422728861077/250375000000000000000000000000000 : ℝ)*base76 + (1371293990074861077/250375000000000000000000000000000 : ℝ)*base78 + (3098058370735013923/250375000000000000000000000000000 : ℝ)*base79 + (15797194191749/5007500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4135527/500000000000000000000 : ℝ)*base89 + (4135527/500000000000000000000 : ℝ)*base91 + (4135527/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1183_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10753/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1183_s5_0 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-16775761/78125000 : ℝ)*x 0 + (1348464241/2500000000 : ℝ)*x 1 + (329056097/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16775761/78125000 : ℝ)^1047 ≤ (13051641901057/100000000000000 : ℝ)^791 := by
    have hnat : (16775761 : ℕ)^1047*100000000000000^791 ≤ 13051641901057^791*78125000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16775761 78125000 13051641901057 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348464241/2500000000 : ℝ)^1047 ≤ (44170376181843/100000000000000 : ℝ)^791 := by
    have hnat : (1348464241 : ℕ)^1047*100000000000000^791 ≤ 44170376181843^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348464241 2500000000 44170376181843 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329056097/625000000 : ℝ)^1047 ≤ (42777981899287/100000000000000 : ℝ)^791 := by
    have hnat : (329056097 : ℕ)^1047*100000000000000^791 ≤ 42777981899287^791*625000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329056097 625000000 42777981899287 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16775761/78125000 : ℝ), (1348464241/2500000000 : ℝ), (329056097/625000000 : ℝ)] ![(13051641901057/100000000000000 : ℝ), (44170376181843/100000000000000 : ℝ), (42777981899287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16775761/78125000 : ℝ)|^1047 ≤ (13051641901057/100000000000000 : ℝ)^791
        have hw : |(-16775761/78125000 : ℝ)|=(16775761/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348464241/2500000000 : ℝ)|^1047 ≤ (44170376181843/100000000000000 : ℝ)^791
        have hw : |(1348464241/2500000000 : ℝ)|=(1348464241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329056097/625000000 : ℝ)|^1047 ≤ (42777981899287/100000000000000 : ℝ)^791
        have hw : |(329056097/625000000 : ℝ)|=(329056097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s5_1 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344988647/10000000000 : ℝ)*x 0 + (-1106359879/5000000000 : ℝ)*x 1 + (2632448777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344988647/10000000000 : ℝ)^1047 ≤ (10910363810051/25000000000000 : ℝ)^791 := by
    have hnat : (5344988647 : ℕ)^1047*25000000000000^791 ≤ 10910363810051^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344988647 10000000000 10910363810051 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106359879/5000000000 : ℝ)^1047 ≤ (6790281412607/50000000000000 : ℝ)^791 := by
    have hnat : (1106359879 : ℕ)^1047*50000000000000^791 ≤ 6790281412607^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106359879 5000000000 6790281412607 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632448777/5000000000 : ℝ)^1047 ≤ (10694495480199/25000000000000 : ℝ)^791 := by
    have hnat : (2632448777 : ℕ)^1047*25000000000000^791 ≤ 10694495480199^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632448777 5000000000 10694495480199 25000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344988647/10000000000 : ℝ), (-1106359879/5000000000 : ℝ), (2632448777/5000000000 : ℝ)] ![(10910363810051/25000000000000 : ℝ), (6790281412607/50000000000000 : ℝ), (10694495480199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344988647/10000000000 : ℝ)|^1047 ≤ (10910363810051/25000000000000 : ℝ)^791
        have hw : |(5344988647/10000000000 : ℝ)|=(5344988647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106359879/5000000000 : ℝ)|^1047 ≤ (6790281412607/50000000000000 : ℝ)^791
        have hw : |(-1106359879/5000000000 : ℝ)|=(1106359879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632448777/5000000000 : ℝ)|^1047 ≤ (10694495480199/25000000000000 : ℝ)^791
        have hw : |(2632448777/5000000000 : ℝ)|=(2632448777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s5_2 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336247161/2500000000 : ℝ)*x 0 + (5264897557/10000000000 : ℝ)*x 1 + (-1106359879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336247161/2500000000 : ℝ)^1047 ≤ (21820727603891/50000000000000 : ℝ)^791 := by
    have hnat : (1336247161 : ℕ)^1047*50000000000000^791 ≤ 21820727603891^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336247161 2500000000 21820727603891 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264897557/10000000000 : ℝ)^1047 ≤ (2138899097653/5000000000000 : ℝ)^791 := by
    have hnat : (5264897557 : ℕ)^1047*5000000000000^791 ≤ 2138899097653^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264897557 10000000000 2138899097653 5000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106359879/5000000000 : ℝ)^1047 ≤ (6790281412607/50000000000000 : ℝ)^791 := by
    have hnat : (1106359879 : ℕ)^1047*50000000000000^791 ≤ 6790281412607^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106359879 5000000000 6790281412607 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336247161/2500000000 : ℝ), (5264897557/10000000000 : ℝ), (-1106359879/5000000000 : ℝ)] ![(21820727603891/50000000000000 : ℝ), (2138899097653/5000000000000 : ℝ), (6790281412607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336247161/2500000000 : ℝ)|^1047 ≤ (21820727603891/50000000000000 : ℝ)^791
        have hw : |(1336247161/2500000000 : ℝ)|=(1336247161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264897557/10000000000 : ℝ)|^1047 ≤ (2138899097653/5000000000000 : ℝ)^791
        have hw : |(5264897557/10000000000 : ℝ)|=(5264897557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106359879/5000000000 : ℝ)|^1047 ≤ (6790281412607/50000000000000 : ℝ)^791
        have hw : |(-1106359879/5000000000 : ℝ)|=(1106359879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s5_3 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2179425391/5000000000 : ℝ)*x 0 + (2115714053/5000000000 : ℝ)*x 1 + (4490054373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179425391/5000000000 : ℝ)^1047 ≤ (33316395589323/100000000000000 : ℝ)^791 := by
    have hnat : (2179425391 : ℕ)^1047*100000000000000^791 ≤ 33316395589323^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179425391 5000000000 33316395589323 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115714053/5000000000 : ℝ)^1047 ≤ (2002086635843/6250000000000 : ℝ)^791 := by
    have hnat : (2115714053 : ℕ)^1047*6250000000000^791 ≤ 2002086635843^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115714053 5000000000 2002086635843 6250000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490054373/10000000000 : ℝ)^1047 ≤ (6930043642437/20000000000000 : ℝ)^791 := by
    have hnat : (4490054373 : ℕ)^1047*20000000000000^791 ≤ 6930043642437^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490054373 10000000000 6930043642437 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179425391/5000000000 : ℝ), (2115714053/5000000000 : ℝ), (4490054373/10000000000 : ℝ)] ![(33316395589323/100000000000000 : ℝ), (2002086635843/6250000000000 : ℝ), (6930043642437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179425391/5000000000 : ℝ)|^1047 ≤ (33316395589323/100000000000000 : ℝ)^791
        have hw : |(2179425391/5000000000 : ℝ)|=(2179425391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115714053/5000000000 : ℝ)|^1047 ≤ (2002086635843/6250000000000 : ℝ)^791
        have hw : |(2115714053/5000000000 : ℝ)|=(2115714053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490054373/10000000000 : ℝ)|^1047 ≤ (6930043642437/20000000000000 : ℝ)^791
        have hw : |(4490054373/10000000000 : ℝ)|=(4490054373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s5_4 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-268412817/1250000000 : ℝ)*x 0 + (2632614957/5000000000 : ℝ)*x 1 + (5393523383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268412817/1250000000 : ℝ)^1047 ≤ (6525841578729/50000000000000 : ℝ)^791 := by
    have hnat : (268412817 : ℕ)^1047*50000000000000^791 ≤ 6525841578729^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268412817 1250000000 6525841578729 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632614957/5000000000 : ℝ)^1047 ≤ (2673847275503/6250000000000 : ℝ)^791 := by
    have hnat : (2632614957 : ℕ)^1047*6250000000000^791 ≤ 2673847275503^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632614957 5000000000 2673847275503 6250000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393523383/10000000000 : ℝ)^1047 ≤ (5520845053527/12500000000000 : ℝ)^791 := by
    have hnat : (5393523383 : ℕ)^1047*12500000000000^791 ≤ 5520845053527^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393523383 10000000000 5520845053527 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268412817/1250000000 : ℝ), (2632614957/5000000000 : ℝ), (5393523383/10000000000 : ℝ)] ![(6525841578729/50000000000000 : ℝ), (2673847275503/6250000000000 : ℝ), (5520845053527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268412817/1250000000 : ℝ)|^1047 ≤ (6525841578729/50000000000000 : ℝ)^791
        have hw : |(-268412817/1250000000 : ℝ)|=(268412817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632614957/5000000000 : ℝ)|^1047 ≤ (2673847275503/6250000000000 : ℝ)^791
        have hw : |(2632614957/5000000000 : ℝ)|=(2632614957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393523383/10000000000 : ℝ)|^1047 ≤ (5520845053527/12500000000000 : ℝ)^791
        have hw : |(5393523383/10000000000 : ℝ)|=(5393523383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s5_5 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656109581/5000000000 : ℝ)*x 0 + (-521023447/2500000000 : ℝ)*x 1 + (5393523341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656109581/5000000000 : ℝ)^1047 ≤ (2705478312669/6250000000000 : ℝ)^791 := by
    have hnat : (2656109581 : ℕ)^1047*6250000000000^791 ≤ 2705478312669^791*5000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656109581 5000000000 2705478312669 6250000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521023447/2500000000 : ℝ)^1047 ≤ (1568198374877/12500000000000 : ℝ)^791 := by
    have hnat : (521023447 : ℕ)^1047*12500000000000^791 ≤ 1568198374877^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521023447 2500000000 1568198374877 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393523341/10000000000 : ℝ)^1047 ≤ (22083379986487/50000000000000 : ℝ)^791 := by
    have hnat : (5393523341 : ℕ)^1047*50000000000000^791 ≤ 22083379986487^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393523341 10000000000 22083379986487 50000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656109581/5000000000 : ℝ), (-521023447/2500000000 : ℝ), (5393523341/10000000000 : ℝ)] ![(2705478312669/6250000000000 : ℝ), (1568198374877/12500000000000 : ℝ), (22083379986487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656109581/5000000000 : ℝ)|^1047 ≤ (2705478312669/6250000000000 : ℝ)^791
        have hw : |(2656109581/5000000000 : ℝ)|=(2656109581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521023447/2500000000 : ℝ)|^1047 ≤ (1568198374877/12500000000000 : ℝ)^791
        have hw : |(-521023447/2500000000 : ℝ)|=(521023447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393523341/10000000000 : ℝ)|^1047 ≤ (22083379986487/50000000000000 : ℝ)^791
        have hw : |(5393523341/10000000000 : ℝ)|=(5393523341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s5_6 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312218909/10000000000 : ℝ)*x 0 + (13483809/25000000 : ℝ)*x 1 + (-2084093779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312218909/10000000000 : ℝ)^1047 ≤ (43287650273859/100000000000000 : ℝ)^791 := by
    have hnat : (5312218909 : ℕ)^1047*100000000000000^791 ≤ 43287650273859^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312218909 10000000000 43287650273859 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13483809/25000000 : ℝ)^1047 ≤ (441667627803/1000000000000 : ℝ)^791 := by
    have hnat : (13483809 : ℕ)^1047*1000000000000^791 ≤ 441667627803^791*25000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13483809 25000000 441667627803 1000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084093779/10000000000 : ℝ)^1047 ≤ (2509117385461/20000000000000 : ℝ)^791 := by
    have hnat : (2084093779 : ℕ)^1047*20000000000000^791 ≤ 2509117385461^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084093779 10000000000 2509117385461 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312218909/10000000000 : ℝ), (13483809/25000000 : ℝ), (-2084093779/10000000000 : ℝ)] ![(43287650273859/100000000000000 : ℝ), (441667627803/1000000000000 : ℝ), (2509117385461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312218909/10000000000 : ℝ)|^1047 ≤ (43287650273859/100000000000000 : ℝ)^791
        have hw : |(5312218909/10000000000 : ℝ)|=(5312218909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13483809/25000000 : ℝ)|^1047 ≤ (441667627803/1000000000000 : ℝ)^791
        have hw : |(13483809/25000000 : ℝ)|=(13483809/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084093779/10000000000 : ℝ)|^1047 ≤ (2509117385461/20000000000000 : ℝ)^791
        have hw : |(-2084093779/10000000000 : ℝ)|=(2084093779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1183_s5_7 (p : ℝ) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1089715259/2500000000 : ℝ)*x 0 + (561173483/1250000000 : ℝ)*x 1 + (4232097151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089715259/2500000000 : ℝ)^1047 ≤ (6663299866029/20000000000000 : ℝ)^791 := by
    have hnat : (1089715259 : ℕ)^1047*20000000000000^791 ≤ 6663299866029^791*2500000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089715259 2500000000 6663299866029 20000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561173483/1250000000 : ℝ)^1047 ≤ (4330426275327/12500000000000 : ℝ)^791 := by
    have hnat : (561173483 : ℕ)^1047*12500000000000^791 ≤ 4330426275327^791*1250000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561173483 1250000000 4330426275327 12500000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232097151/10000000000 : ℝ)^1047 ≤ (32040090459321/100000000000000 : ℝ)^791 := by
    have hnat : (4232097151 : ℕ)^1047*100000000000000^791 ≤ 32040090459321^791*10000000000^1047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232097151 10000000000 32040090459321 100000000000000 1047 791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1047/256 : ℝ)) 1047 791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089715259/2500000000 : ℝ), (561173483/1250000000 : ℝ), (4232097151/10000000000 : ℝ)] ![(6663299866029/20000000000000 : ℝ), (4330426275327/12500000000000 : ℝ), (32040090459321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089715259/2500000000 : ℝ)|^1047 ≤ (6663299866029/20000000000000 : ℝ)^791
        have hw : |(1089715259/2500000000 : ℝ)|=(1089715259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561173483/1250000000 : ℝ)|^1047 ≤ (4330426275327/12500000000000 : ℝ)^791
        have hw : |(561173483/1250000000 : ℝ)|=(561173483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232097151/10000000000 : ℝ)|^1047 ≤ (32040090459321/100000000000000 : ℝ)^791
        have hw : |(4232097151/10000000000 : ℝ)|=(4232097151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1183_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5687/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7053/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11251/100000 : ℝ) ^ (8375/2048 : ℝ) ≤ (13182058569589047/100000000000000000000 : ℝ) := by
    have hpowers : (11251/100000 : ℝ)^8375 ≤ (13182058569589047/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11251 : ℕ)^8375*100000000000000000000^2048 ≤ 13182058569589047^2048*100000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11251 100000 13182058569589047 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11251/100000 : ℝ)) (X := (13182058569589047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8375/2048 : ℝ) ≤ (34486806455760931/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8375 ≤ (34486806455760931/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8375*100000000000000000000^2048 ≤ 34486806455760931^2048*50000^8375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 34486806455760931 100000000000000000000 8375 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (34486806455760931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013182058569589047/50000000000000000000 : ℝ) ≤ (10000644636844631/10000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50013182058569589047/50000000000000000000 : ℝ)^2048 ≤ (10000644636844631/10000000000000000 : ℝ)^8375 := by
      have hnat : (50013182058569589047 : ℕ)^2048*10000000000000000^8375 ≤ 10000644636844631^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013182058569589047 50000000000000000000 10000644636844631 10000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000644636844631/10000000000000000 : ℝ)) (X := (50013182058569589047/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023834432512674989/50000000000000000000 : ℝ) ≤ (500058273589219/500000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50023834432512674989/50000000000000000000 : ℝ)^2048 ≤ (500058273589219/500000000000000 : ℝ)^8375 := by
      have hnat : (50023834432512674989 : ℕ)^2048*500000000000000^8375 ≤ 500058273589219^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023834432512674989 50000000000000000000 500058273589219 500000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500058273589219/500000000000000 : ℝ)) (X := (50023834432512674989/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034486806455760931/50000000000000000000 : ℝ) ≤ (10001686306724129/10000000000000000 : ℝ) ^ (8375/2048 : ℝ) := by
    have hpowers : (50034486806455760931/50000000000000000000 : ℝ)^2048 ≤ (10001686306724129/10000000000000000 : ℝ)^8375 := by
      have hnat : (50034486806455760931 : ℕ)^2048*10000000000000000^8375 ≤ 10001686306724129^8375*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034486806455760931 50000000000000000000 10001686306724129 10000000000000000 2048 8375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001686306724129/10000000000000000 : ℝ)) (X := (50034486806455760931/50000000000000000000 : ℝ)) (by norm_num) 8375 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13182058569589047/100000000000000000000 : ℝ) ≤ ((1192808124955732091/1193200000000000000 : ℝ)+2*(520834939749/298300000000000 : ℝ)*(11251/100000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (1192808124955732091/1193200000000000000 : ℝ)+2*(520834939749/298300000000000 : ℝ)*(11251/100000 : ℝ)=(10000644636844631/10000000000000000 : ℝ) by norm_num, show 1+2*(13182058569589047/100000000000000000000 : ℝ)=(50013182058569589047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34486806455760931/100000000000000000000 : ℝ)+(13182058569589047/100000000000000000000 : ℝ) ≤ ((1192808124955732091/1193200000000000000 : ℝ)+(520834939749/298300000000000 : ℝ)*((7117/50000 : ℝ)+(11251/100000 : ℝ)))^(8375/2048 : ℝ) := by
    rw [show (1192808124955732091/1193200000000000000 : ℝ)+(520834939749/298300000000000 : ℝ)*((7117/50000 : ℝ)+(11251/100000 : ℝ))=(500058273589219/500000000000000 : ℝ) by norm_num, show 1+(34486806455760931/100000000000000000000 : ℝ)+(13182058569589047/100000000000000000000 : ℝ)=(50023834432512674989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34486806455760931/100000000000000000000 : ℝ) ≤ ((1192808124955732091/1193200000000000000 : ℝ)+2*(520834939749/298300000000000 : ℝ)*(7117/50000 : ℝ))^(8375/2048 : ℝ) := by
    rw [show (1192808124955732091/1193200000000000000 : ℝ)+2*(520834939749/298300000000000 : ℝ)*(7117/50000 : ℝ)=(10001686306724129/10000000000000000 : ℝ) by norm_num, show 1+2*(34486806455760931/100000000000000000000 : ℝ)=(50034486806455760931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1192808124955732091/1193200000000000000 : ℝ)*(X 1 0+X 2 0)+(520834939749/298300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1192808124955732091/1193200000000000000 : ℝ)) (alpha := (520834939749/298300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1192808124955732091/1193200000000000000 : ℝ)*(X 0 1+X 2 1)+(520834939749/298300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1192808124955732091/1193200000000000000 : ℝ)) (alpha := (520834939749/298300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1192808124955732091/1193200000000000000 : ℝ)*(X 0 2+X 1 2)+(520834939749/298300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8375/2048 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1192808124955732091/1193200000000000000 : ℝ)) (alpha := (520834939749/298300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16775761/78125000 : ℝ)*X 0 0+(1348464241/2500000000 : ℝ)*X 0 1+(329056097/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344988647/10000000000 : ℝ)*X 1 0+(-1106359879/5000000000 : ℝ)*X 1 1+(2632448777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336247161/2500000000 : ℝ)*X 2 0+(5264897557/10000000000 : ℝ)*X 2 1+(-1106359879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179425391/5000000000 : ℝ)*X 0 0+(2115714053/5000000000 : ℝ)*X 0 1+(4490054373/10000000000 : ℝ)*X 0 2+(2179425391/5000000000 : ℝ)*X 1 0+(2115714053/5000000000 : ℝ)*X 1 1+(4490054373/10000000000 : ℝ)*X 1 2+(2179425391/5000000000 : ℝ)*X 2 0+(2115714053/5000000000 : ℝ)*X 2 1+(4490054373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268412817/1250000000 : ℝ)*X 0 0+(2632614957/5000000000 : ℝ)*X 0 1+(5393523383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656109581/5000000000 : ℝ)*X 1 0+(-521023447/2500000000 : ℝ)*X 1 1+(5393523341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312218909/10000000000 : ℝ)*X 2 0+(13483809/25000000 : ℝ)*X 2 1+(-2084093779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089715259/2500000000 : ℝ)*X 0 0+(561173483/1250000000 : ℝ)*X 0 1+(4232097151/10000000000 : ℝ)*X 0 2+(1089715259/2500000000 : ℝ)*X 1 0+(561173483/1250000000 : ℝ)*X 1 1+(4232097151/10000000000 : ℝ)*X 1 2+(1089715259/2500000000 : ℝ)*X 2 0+(561173483/1250000000 : ℝ)*X 2 1+(4232097151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1183_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (390181943487734918992807953/59660000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1284513607/100000000000000 : ℝ)*(base19) + (1187518691/100000000000000 : ℝ)*(base23) + (49517337/100000000000000 : ℝ)*(lower2) + (167495603/100000000000000 : ℝ)*(upper3) + (24532293/25000000000000 : ℝ)*(upper5) + (5810533477696161/100000000000000 : ℝ)*(major0) + (5810533477696161/100000000000000 : ℝ)*(major1) + (5810533477696161/100000000000000 : ℝ)*(major2) + (7754413994030521/100000000000000 : ℝ)*(sp0) + (3877223547480697/50000000000000 : ℝ)*(sp1) + (7754447191956309/100000000000000 : ℝ)*(sp2) + (1933299922755879/50000000000000 : ℝ)*(sp3) + (34385444479/100000000000000 : ℝ)*(sp4) + (2314050307/12500000000000 : ℝ)*(sp7) + (1933309178957107/50000000000000 : ℝ)*(f.failure) + (7754448379475001/100000000000000 : ℝ)*(f.sum) + (227092610873311/14915000000000000000000000000 : ℝ)*base66 + (1192198587409318651/119320000000000000000000000000000 : ℝ)*base67 + (1755955726744078651/119320000000000000000000000000000 : ℝ)*base69 + (442030291269241349/119320000000000000000000000000000 : ℝ)*base72 + (9215714946389/14915000000000000000000000000 : ℝ)*base73 + (1111792277101561349/119320000000000000000000000000000 : ℝ)*base76 + (1386550835096201349/119320000000000000000000000000000 : ℝ)*base78 + (497789524187841349/119320000000000000000000000000000 : ℝ)*base80 + (521378309869/14915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (7932913/1000000000000000000000 : ℝ)*base89 + (7932913/1000000000000000000000 : ℝ)*base91 + (7932913/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36302185557314007440302161/3728750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2061656711/100000000000000 : ℝ)*(base19) + (1810206717/100000000000000 : ℝ)*(base23) + (42822457/25000000000000 : ℝ)*(upper3) + (30346231/50000000000000 : ℝ)*(lower4) + (36775613/20000000000000 : ℝ)*(upper5) + (730079745273493/12500000000000 : ℝ)*(major0) + (730079745273493/12500000000000 : ℝ)*(major1) + (730079745273493/12500000000000 : ℝ)*(major2) + (57972053809/100000000000000 : ℝ)*(sp1) + (29433739957/50000000000000 : ℝ)*(sp2) + (1558924843732573/20000000000000 : ℝ)*(sp4) + (974320523119043/12500000000000 : ℝ)*(sp5) + (7794563540976233/100000000000000 : ℝ)*(sp6) + (3886651381187943/100000000000000 : ℝ)*(sp7) + (3886651381187943/100000000000000 : ℝ)*(f.failure) + (1558924843732573/20000000000000 : ℝ)*(f.sum) + (19134084611809/3728750000000000000000000000 : ℝ)*base65 + (134927272220561863/14915000000000000000000000000000 : ℝ)*base67 + (93290950966728137/14915000000000000000000000000000 : ℝ)*base70 + (98290905383206863/14915000000000000000000000000000 : ℝ)*base71 + (27862994282493/7457500000000000000000000000 : ℝ)*base73 + (349298665244846863/14915000000000000000000000000000 : ℝ)*base75 + (154094419415476863/14915000000000000000000000000000 : ℝ)*base77 + (257068813050041863/14915000000000000000000000000000 : ℝ)*base79 + (32185893628673/7457500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (634963/2000000000000000000000 : ℝ)*base90 + (634963/2000000000000000000000 : ℝ)*base92 + (634963/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1183_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1183_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1183_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2313/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1183_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1183_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1183_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8375/2048 : ℝ) ≤ p) (hpb : p ≤ (1047/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30054859/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2313/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1183_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
