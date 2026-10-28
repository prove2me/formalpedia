-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1061_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:03:25.466324+00:00
-- url     : https://prove2.me/submissions/06523d5e-9124-4bfe-917a-0283b1c94f84

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
theorem support_rectangle_w1061_s3_0 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201426209/10000000000 : ℝ)*x 0 + (1359529603/2500000000 : ℝ)*x 1 + (652978609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201426209/10000000000 : ℝ)^4127 ≤ (6679814197207/50000000000000 : ℝ)^3103 := by
    have hnat : (2201426209 : ℕ)^4127*50000000000000^3103 ≤ 6679814197207^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201426209 10000000000 6679814197207 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359529603/2500000000 : ℝ)^4127 ≤ (22239031470011/50000000000000 : ℝ)^3103 := by
    have hnat : (1359529603 : ℕ)^4127*50000000000000^3103 ≤ 22239031470011^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359529603 2500000000 22239031470011 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652978609/1250000000 : ℝ)^4127 ≤ (21081154326561/50000000000000 : ℝ)^3103 := by
    have hnat : (652978609 : ℕ)^4127*50000000000000^3103 ≤ 21081154326561^3103*1250000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652978609 1250000000 21081154326561 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201426209/10000000000 : ℝ), (1359529603/2500000000 : ℝ), (652978609/1250000000 : ℝ)] ![(6679814197207/50000000000000 : ℝ), (22239031470011/50000000000000 : ℝ), (21081154326561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201426209/10000000000 : ℝ)|^4127 ≤ (6679814197207/50000000000000 : ℝ)^3103
        have hw : |(-2201426209/10000000000 : ℝ)|=(2201426209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359529603/2500000000 : ℝ)|^4127 ≤ (22239031470011/50000000000000 : ℝ)^3103
        have hw : |(1359529603/2500000000 : ℝ)|=(1359529603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652978609/1250000000 : ℝ)|^4127 ≤ (21081154326561/50000000000000 : ℝ)^3103
        have hw : |(652978609/1250000000 : ℝ)|=(652978609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s3_1 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677909649/5000000000 : ℝ)*x 0 + (-2311173211/10000000000 : ℝ)*x 1 + (5223829021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677909649/5000000000 : ℝ)^4127 ≤ (43585054568079/100000000000000 : ℝ)^3103 := by
    have hnat : (2677909649 : ℕ)^4127*100000000000000^3103 ≤ 43585054568079^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677909649 5000000000 43585054568079 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2311173211/10000000000 : ℝ)^4127 ≤ (14252635156651/100000000000000 : ℝ)^3103 := by
    have hnat : (2311173211 : ℕ)^4127*100000000000000^3103 ≤ 14252635156651^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311173211 10000000000 14252635156651 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223829021/10000000000 : ℝ)^4127 ≤ (21081155126293/50000000000000 : ℝ)^3103 := by
    have hnat : (5223829021 : ℕ)^4127*50000000000000^3103 ≤ 21081155126293^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223829021 10000000000 21081155126293 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677909649/5000000000 : ℝ), (-2311173211/10000000000 : ℝ), (5223829021/10000000000 : ℝ)] ![(43585054568079/100000000000000 : ℝ), (14252635156651/100000000000000 : ℝ), (21081155126293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677909649/5000000000 : ℝ)|^4127 ≤ (43585054568079/100000000000000 : ℝ)^3103
        have hw : |(2677909649/5000000000 : ℝ)|=(2677909649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2311173211/10000000000 : ℝ)|^4127 ≤ (14252635156651/100000000000000 : ℝ)^3103
        have hw : |(-2311173211/10000000000 : ℝ)|=(2311173211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223829021/10000000000 : ℝ)|^4127 ≤ (21081155126293/50000000000000 : ℝ)^3103
        have hw : |(5223829021/10000000000 : ℝ)|=(5223829021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s3_2 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355819319/10000000000 : ℝ)*x 0 + (1044765867/2000000000 : ℝ)*x 1 + (-577793193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355819319/10000000000 : ℝ)^4127 ≤ (43585054795371/100000000000000 : ℝ)^3103 := by
    have hnat : (5355819319 : ℕ)^4127*100000000000000^3103 ≤ 43585054795371^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355819319 10000000000 43585054795371 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044765867/2000000000 : ℝ)^4127 ≤ (10540578405817/25000000000000 : ℝ)^3103 := by
    have hnat : (1044765867 : ℕ)^4127*25000000000000^3103 ≤ 10540578405817^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044765867 2000000000 10540578405817 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (577793193/2500000000 : ℝ)^4127 ≤ (14252631556009/100000000000000 : ℝ)^3103 := by
    have hnat : (577793193 : ℕ)^4127*100000000000000^3103 ≤ 14252631556009^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577793193 2500000000 14252631556009 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355819319/10000000000 : ℝ), (1044765867/2000000000 : ℝ), (-577793193/2500000000 : ℝ)] ![(43585054795371/100000000000000 : ℝ), (10540578405817/25000000000000 : ℝ), (14252631556009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355819319/10000000000 : ℝ)|^4127 ≤ (43585054795371/100000000000000 : ℝ)^3103
        have hw : |(5355819319/10000000000 : ℝ)|=(5355819319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044765867/2000000000 : ℝ)|^4127 ≤ (10540578405817/25000000000000 : ℝ)^3103
        have hw : |(1044765867/2000000000 : ℝ)|=(1044765867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-577793193/2500000000 : ℝ)|^4127 ≤ (14252631556009/100000000000000 : ℝ)^3103
        have hw : |(-577793193/2500000000 : ℝ)|=(577793193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s3_3 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093342383/2500000000 : ℝ)*x 0 + (2084342339/5000000000 : ℝ)*x 1 + (4588244041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093342383/2500000000 : ℝ)^4127 ≤ (8321935854169/25000000000000 : ℝ)^3103 := by
    have hnat : (1093342383 : ℕ)^4127*25000000000000^3103 ≤ 8321935854169^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093342383 2500000000 8321935854169 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084342339/5000000000 : ℝ)^4127 ≤ (6246367072531/20000000000000 : ℝ)^3103 := by
    have hnat : (2084342339 : ℕ)^4127*20000000000000^3103 ≤ 6246367072531^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084342339 5000000000 6246367072531 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4588244041/10000000000 : ℝ)^4127 ≤ (35480421202707/100000000000000 : ℝ)^3103 := by
    have hnat : (4588244041 : ℕ)^4127*100000000000000^3103 ≤ 35480421202707^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4588244041 10000000000 35480421202707 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093342383/2500000000 : ℝ), (2084342339/5000000000 : ℝ), (4588244041/10000000000 : ℝ)] ![(8321935854169/25000000000000 : ℝ), (6246367072531/20000000000000 : ℝ), (35480421202707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093342383/2500000000 : ℝ)|^4127 ≤ (8321935854169/25000000000000 : ℝ)^3103
        have hw : |(1093342383/2500000000 : ℝ)|=(1093342383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084342339/5000000000 : ℝ)|^4127 ≤ (6246367072531/20000000000000 : ℝ)^3103
        have hw : |(2084342339/5000000000 : ℝ)|=(2084342339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4588244041/10000000000 : ℝ)|^4127 ≤ (35480421202707/100000000000000 : ℝ)^3103
        have hw : |(4588244041/10000000000 : ℝ)|=(4588244041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s3_4 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201449163/10000000000 : ℝ)*x 0 + (522471097/1000000000 : ℝ)*x 1 + (271861543/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201449163/10000000000 : ℝ)^4127 ≤ (6679906831559/50000000000000 : ℝ)^3103 := by
    have hnat : (2201449163 : ℕ)^4127*50000000000000^3103 ≤ 6679906831559^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201449163 10000000000 6679906831559 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522471097/1000000000 : ℝ)^4127 ≤ (42171777935603/100000000000000 : ℝ)^3103 := by
    have hnat : (522471097 : ℕ)^4127*100000000000000^3103 ≤ 42171777935603^3103*1000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522471097 1000000000 42171777935603 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271861543/500000000 : ℝ)^4127 ≤ (8893681678123/20000000000000 : ℝ)^3103 := by
    have hnat : (271861543 : ℕ)^4127*20000000000000^3103 ≤ 8893681678123^3103*500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271861543 500000000 8893681678123 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201449163/10000000000 : ℝ), (522471097/1000000000 : ℝ), (271861543/500000000 : ℝ)] ![(6679906831559/50000000000000 : ℝ), (42171777935603/100000000000000 : ℝ), (8893681678123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201449163/10000000000 : ℝ)|^4127 ≤ (6679906831559/50000000000000 : ℝ)^3103
        have hw : |(-2201449163/10000000000 : ℝ)|=(2201449163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522471097/1000000000 : ℝ)|^4127 ≤ (42171777935603/100000000000000 : ℝ)^3103
        have hw : |(522471097/1000000000 : ℝ)|=(522471097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271861543/500000000 : ℝ)|^4127 ≤ (8893681678123/20000000000000 : ℝ)^3103
        have hw : |(271861543/500000000 : ℝ)|=(271861543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s3_5 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301861711/10000000000 : ℝ)*x 0 + (-2097770487/10000000000 : ℝ)*x 1 + (5437231477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301861711/10000000000 : ℝ)^4127 ≤ (21501011063841/50000000000000 : ℝ)^3103 := by
    have hnat : (5301861711 : ℕ)^4127*50000000000000^3103 ≤ 21501011063841^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301861711 10000000000 21501011063841 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097770487/10000000000 : ℝ)^4127 ≤ (12529562760741/100000000000000 : ℝ)^3103 := by
    have hnat : (2097770487 : ℕ)^4127*100000000000000^3103 ≤ 12529562760741^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097770487 10000000000 12529562760741 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437231477/10000000000 : ℝ)^4127 ≤ (5558551887749/12500000000000 : ℝ)^3103 := by
    have hnat : (5437231477 : ℕ)^4127*12500000000000^3103 ≤ 5558551887749^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437231477 10000000000 5558551887749 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301861711/10000000000 : ℝ), (-2097770487/10000000000 : ℝ), (5437231477/10000000000 : ℝ)] ![(21501011063841/50000000000000 : ℝ), (12529562760741/100000000000000 : ℝ), (5558551887749/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301861711/10000000000 : ℝ)|^4127 ≤ (21501011063841/50000000000000 : ℝ)^3103
        have hw : |(5301861711/10000000000 : ℝ)|=(5301861711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097770487/10000000000 : ℝ)|^4127 ≤ (12529562760741/100000000000000 : ℝ)^3103
        have hw : |(-2097770487/10000000000 : ℝ)|=(2097770487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437231477/10000000000 : ℝ)|^4127 ≤ (5558551887749/12500000000000 : ℝ)^3103
        have hw : |(5437231477/10000000000 : ℝ)|=(5437231477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s3_6 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662732667/1250000000 : ℝ)*x 0 + (5437231343/10000000000 : ℝ)*x 1 + (-1048885589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662732667/1250000000 : ℝ)^4127 ≤ (1075050452061/2500000000000 : ℝ)^3103 := by
    have hnat : (662732667 : ℕ)^4127*2500000000000^3103 ≤ 1075050452061^3103*1250000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662732667 1250000000 1075050452061 2500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437231343/10000000000 : ℝ)^4127 ≤ (347409481597/781250000000 : ℝ)^3103 := by
    have hnat : (5437231343 : ℕ)^4127*781250000000^3103 ≤ 347409481597^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437231343 10000000000 347409481597 781250000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048885589/5000000000 : ℝ)^4127 ≤ (12529568249937/100000000000000 : ℝ)^3103 := by
    have hnat : (1048885589 : ℕ)^4127*100000000000000^3103 ≤ 12529568249937^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048885589 5000000000 12529568249937 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662732667/1250000000 : ℝ), (5437231343/10000000000 : ℝ), (-1048885589/5000000000 : ℝ)] ![(1075050452061/2500000000000 : ℝ), (347409481597/781250000000 : ℝ), (12529568249937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662732667/1250000000 : ℝ)|^4127 ≤ (1075050452061/2500000000000 : ℝ)^3103
        have hw : |(662732667/1250000000 : ℝ)|=(662732667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437231343/10000000000 : ℝ)|^4127 ≤ (347409481597/781250000000 : ℝ)^3103
        have hw : |(5437231343/10000000000 : ℝ)|=(5437231343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048885589/5000000000 : ℝ)|^4127 ≤ (12529568249937/100000000000000 : ℝ)^3103
        have hw : |(-1048885589/5000000000 : ℝ)|=(1048885589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s3_7 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4373413541/10000000000 : ℝ)*x 0 + (71664353/156250000 : ℝ)*x 1 + (4170420663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373413541/10000000000 : ℝ)^4127 ≤ (1664409446623/5000000000000 : ℝ)^3103 := by
    have hnat : (4373413541 : ℕ)^4127*5000000000000^3103 ≤ 1664409446623^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373413541 10000000000 1664409446623 5000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71664353/156250000 : ℝ)^4127 ≤ (8865669110707/25000000000000 : ℝ)^3103 := by
    have hnat : (71664353 : ℕ)^4127*25000000000000^3103 ≤ 8865669110707^3103*156250000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71664353 156250000 8865669110707 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170420663/10000000000 : ℝ)^4127 ≤ (31249134600101/100000000000000 : ℝ)^3103 := by
    have hnat : (4170420663 : ℕ)^4127*100000000000000^3103 ≤ 31249134600101^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170420663 10000000000 31249134600101 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373413541/10000000000 : ℝ), (71664353/156250000 : ℝ), (4170420663/10000000000 : ℝ)] ![(1664409446623/5000000000000 : ℝ), (8865669110707/25000000000000 : ℝ), (31249134600101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373413541/10000000000 : ℝ)|^4127 ≤ (1664409446623/5000000000000 : ℝ)^3103
        have hw : |(4373413541/10000000000 : ℝ)|=(4373413541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71664353/156250000 : ℝ)|^4127 ≤ (8865669110707/25000000000000 : ℝ)^3103
        have hw : |(71664353/156250000 : ℝ)|=(71664353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170420663/10000000000 : ℝ)|^4127 ≤ (31249134600101/100000000000000 : ℝ)^3103
        have hw : |(4170420663/10000000000 : ℝ)|=(4170420663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1061_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8687/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14913/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8687/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8687/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8687/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8687/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8687/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8687/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8687/100000 : ℝ) ^ (8253/2048 : ℝ) ≤ (5295090142985761/100000000000000000000 : ℝ) := by
    have hpowers : (8687/100000 : ℝ)^8253 ≤ (5295090142985761/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8687 : ℕ)^8253*100000000000000000000^2048 ≤ 5295090142985761^2048*100000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8687 100000 5295090142985761 100000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8687/100000 : ℝ)) (X := (5295090142985761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16757/100000 : ℝ) ^ (8253/2048 : ℝ) ≤ (74761437497785589/100000000000000000000 : ℝ) := by
    have hpowers : (16757/100000 : ℝ)^8253 ≤ (74761437497785589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16757 : ℕ)^8253*100000000000000000000^2048 ≤ 74761437497785589^2048*100000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16757 100000 74761437497785589 100000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16757/100000 : ℝ)) (X := (74761437497785589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005295090142985761/50000000000000000000 : ℝ) ≤ (10000262787178363/10000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50005295090142985761/50000000000000000000 : ℝ)^2048 ≤ (10000262787178363/10000000000000000 : ℝ)^8253 := by
      have hnat : (50005295090142985761 : ℕ)^2048*10000000000000000^8253 ≤ 10000262787178363^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005295090142985761 50000000000000000000 10000262787178363 10000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000262787178363/10000000000000000 : ℝ)) (X := (50005295090142985761/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2001601130552815427/2000000000000000000 : ℝ) ≤ (1250248252830649/1250000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (2001601130552815427/2000000000000000000 : ℝ)^2048 ≤ (1250248252830649/1250000000000000 : ℝ)^8253 := by
      have hnat : (2001601130552815427 : ℕ)^2048*1250000000000000^8253 ≤ 1250248252830649^8253*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001601130552815427 2000000000000000000 1250248252830649 1250000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250248252830649/1250000000000000 : ℝ)) (X := (2001601130552815427/2000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50074761437497785589/50000000000000000000 : ℝ) ≤ (10003709258112021/10000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50074761437497785589/50000000000000000000 : ℝ)^2048 ≤ (10003709258112021/10000000000000000 : ℝ)^8253 := by
      have hnat : (50074761437497785589 : ℕ)^2048*10000000000000000^8253 ≤ 10003709258112021^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50074761437497785589 50000000000000000000 10003709258112021 10000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003709258112021/10000000000000000 : ℝ)) (X := (50074761437497785589/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5295090142985761/100000000000000000000 : ℝ) ≤ ((20168045299882175591/20175000000000000000 : ℝ)+2*(1723235466829/807000000000000 : ℝ)*(8687/100000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (20168045299882175591/20175000000000000000 : ℝ)+2*(1723235466829/807000000000000 : ℝ)*(8687/100000 : ℝ)=(10000262787178363/10000000000000000 : ℝ) by norm_num, show 1+2*(5295090142985761/100000000000000000000 : ℝ)=(50005295090142985761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74761437497785589/100000000000000000000 : ℝ)+(5295090142985761/100000000000000000000 : ℝ) ≤ ((20168045299882175591/20175000000000000000 : ℝ)+(1723235466829/807000000000000 : ℝ)*((16757/100000 : ℝ)+(8687/100000 : ℝ)))^(8253/2048 : ℝ) := by
    rw [show (20168045299882175591/20175000000000000000 : ℝ)+(1723235466829/807000000000000 : ℝ)*((16757/100000 : ℝ)+(8687/100000 : ℝ))=(1250248252830649/1250000000000000 : ℝ) by norm_num, show 1+(74761437497785589/100000000000000000000 : ℝ)+(5295090142985761/100000000000000000000 : ℝ)=(2001601130552815427/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74761437497785589/100000000000000000000 : ℝ) ≤ ((20168045299882175591/20175000000000000000 : ℝ)+2*(1723235466829/807000000000000 : ℝ)*(16757/100000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (20168045299882175591/20175000000000000000 : ℝ)+2*(1723235466829/807000000000000 : ℝ)*(16757/100000 : ℝ)=(10003709258112021/10000000000000000 : ℝ) by norm_num, show 1+2*(74761437497785589/100000000000000000000 : ℝ)=(50074761437497785589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20168045299882175591/20175000000000000000 : ℝ)*(X 1 0+X 2 0)+(1723235466829/807000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (8687/100000 : ℝ)) (hi := (16757/100000 : ℝ)) (c := (20168045299882175591/20175000000000000000 : ℝ)) (alpha := (1723235466829/807000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20168045299882175591/20175000000000000000 : ℝ)*(X 0 1+X 2 1)+(1723235466829/807000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (8687/100000 : ℝ)) (hi := (16757/100000 : ℝ)) (c := (20168045299882175591/20175000000000000000 : ℝ)) (alpha := (1723235466829/807000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20168045299882175591/20175000000000000000 : ℝ)*(X 0 2+X 1 2)+(1723235466829/807000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (8687/100000 : ℝ)) (hi := (16757/100000 : ℝ)) (c := (20168045299882175591/20175000000000000000 : ℝ)) (alpha := (1723235466829/807000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2201426209/10000000000 : ℝ)*X 0 0+(1359529603/2500000000 : ℝ)*X 0 1+(652978609/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677909649/5000000000 : ℝ)*X 1 0+(-2311173211/10000000000 : ℝ)*X 1 1+(5223829021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355819319/10000000000 : ℝ)*X 2 0+(1044765867/2000000000 : ℝ)*X 2 1+(-577793193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093342383/2500000000 : ℝ)*X 0 0+(2084342339/5000000000 : ℝ)*X 0 1+(4588244041/10000000000 : ℝ)*X 0 2+(1093342383/2500000000 : ℝ)*X 1 0+(2084342339/5000000000 : ℝ)*X 1 1+(4588244041/10000000000 : ℝ)*X 1 2+(1093342383/2500000000 : ℝ)*X 2 0+(2084342339/5000000000 : ℝ)*X 2 1+(4588244041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2201449163/10000000000 : ℝ)*X 0 0+(522471097/1000000000 : ℝ)*X 0 1+(271861543/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301861711/10000000000 : ℝ)*X 1 0+(-2097770487/10000000000 : ℝ)*X 1 1+(5437231477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662732667/1250000000 : ℝ)*X 2 0+(5437231343/10000000000 : ℝ)*X 2 1+(-1048885589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373413541/10000000000 : ℝ)*X 0 0+(71664353/156250000 : ℝ)*X 0 1+(4170420663/10000000000 : ℝ)*X 0 2+(4373413541/10000000000 : ℝ)*X 1 0+(71664353/156250000 : ℝ)*X 1 1+(4170420663/10000000000 : ℝ)*X 1 2+(4373413541/10000000000 : ℝ)*X 2 0+(71664353/156250000 : ℝ)*X 2 1+(4170420663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (353329539196341435523947509/42031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1069739747/50000000000000 : ℝ)*(base19) + (1764028691/100000000000000 : ℝ)*(base23) + (42176933/20000000000000 : ℝ)*(lower2) + (53841421/50000000000000 : ℝ)*(upper3) + (232167303/100000000000000 : ℝ)*(upper5) + (440634747644467/12500000000000 : ℝ)*(major0) + (440634747644467/12500000000000 : ℝ)*(major1) + (440634747644467/12500000000000 : ℝ)*(major2) + (4666621728876183/100000000000000 : ℝ)*(sp0) + (186666627424661/4000000000000 : ℝ)*(sp1) + (72916657204177/1562500000000 : ℝ)*(sp2) + (595867601489773/25000000000000 : ℝ)*(sp3) + (46096219837/100000000000000 : ℝ)*(sp4) + (8725522287/50000000000000 : ℝ)*(sp7) + (2383487857003667/100000000000000 : ℝ)*(f.failure) + (233333391254801/5000000000000 : ℝ)*(f.sum) + (7998043362643/5043750000000000000000000000 : ℝ)*base65 + (967070982184999/84062500000000000000000000000000 : ℝ)*base67 + (56841459438434999/84062500000000000000000000000000 : ℝ)*base69 + (147155502794059999/84062500000000000000000000000000 : ℝ)*base71 + (66267452711003/20175000000000000000000000000 : ℝ)*base74 + (256654102188122499/84062500000000000000000000000000 : ℝ)*base75 + (698655084369684999/84062500000000000000000000000000 : ℝ)*base77 + (953363790736559999/84062500000000000000000000000000 : ℝ)*base79 + (19502750704961/10087500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (50828927/10000000000000000000000 : ℝ)*base89 + (50828927/10000000000000000000000 : ℝ)*base91 + (50828927/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (430103055197963854359136449/84062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1544837127/100000000000000 : ℝ)*(base19) + (47292639/4000000000000 : ℝ)*(base23) + (3622081/10000000000000 : ℝ)*(upper2) + (269841251/100000000000000 : ℝ)*(upper3) + (888589513178313/25000000000000 : ℝ)*(major0) + (888589513178313/25000000000000 : ℝ)*(major1) + (888589513178313/25000000000000 : ℝ)*(major2) + (8497526619/25000000000000 : ℝ)*(sp1) + (12179059033/50000000000000 : ℝ)*(sp2) + (214143143/12500000000000 : ℝ)*(sp3) + (1176357576124059/25000000000000 : ℝ)*(sp4) + (4705394769552633/100000000000000 : ℝ)*(sp5) + (1176351191015549/25000000000000 : ℝ)*(sp6) + (1201641958618097/50000000000000 : ℝ)*(sp7) + (1201642815190669/50000000000000 : ℝ)*(f.failure) + (1176357576124059/25000000000000 : ℝ)*(f.sum) + (786482283073/420312500000000000000000000 : ℝ)*base65 + (667181475942972339/168125000000000000000000000000000 : ℝ)*base68 + (2317122412276722339/168125000000000000000000000000000 : ℝ)*base70 + (3118668098841097339/168125000000000000000000000000000 : ℝ)*base72 + (7796131537107/6725000000000000000000000000 : ℝ)*base74 + (2725939529659847339/168125000000000000000000000000000 : ℝ)*base76 + (1924957397422972339/168125000000000000000000000000000 : ℝ)*base78 + (3374660829969222339/168125000000000000000000000000000 : ℝ)*base80 + (74821510531/52539062500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (55667489/5000000000000000000000 : ℝ)*base89 + (55667489/5000000000000000000000 : ℝ)*base91 + (55667489/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1061_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8687/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14913/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1061_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1061_s4_0 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-441030637/2000000000 : ℝ)*x 0 + (5406093493/10000000000 : ℝ)*x 1 + (1050683847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441030637/2000000000 : ℝ)^4127 ≤ (13389718297577/100000000000000 : ℝ)^3103 := by
    have hnat : (441030637 : ℕ)^4127*100000000000000^3103 ≤ 13389718297577^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441030637 2000000000 13389718297577 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406093493/10000000000 : ℝ)^4127 ≤ (11032508536437/25000000000000 : ℝ)^3103 := by
    have hnat : (5406093493 : ℕ)^4127*25000000000000^3103 ≤ 11032508536437^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406093493 10000000000 11032508536437 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050683847/2000000000 : ℝ)^4127 ≤ (42480247533447/100000000000000 : ℝ)^3103 := by
    have hnat : (1050683847 : ℕ)^4127*100000000000000^3103 ≤ 42480247533447^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050683847 2000000000 42480247533447 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441030637/2000000000 : ℝ), (5406093493/10000000000 : ℝ), (1050683847/2000000000 : ℝ)] ![(13389718297577/100000000000000 : ℝ), (11032508536437/25000000000000 : ℝ), (42480247533447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441030637/2000000000 : ℝ)|^4127 ≤ (13389718297577/100000000000000 : ℝ)^3103
        have hw : |(-441030637/2000000000 : ℝ)|=(441030637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406093493/10000000000 : ℝ)|^4127 ≤ (11032508536437/25000000000000 : ℝ)^3103
        have hw : |(5406093493/10000000000 : ℝ)|=(5406093493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050683847/2000000000 : ℝ)|^4127 ≤ (42480247533447/100000000000000 : ℝ)^3103
        have hw : |(1050683847/2000000000 : ℝ)|=(1050683847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s4_1 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347890331/10000000000 : ℝ)*x 0 + (-456562289/2000000000 : ℝ)*x 1 + (5253420053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347890331/10000000000 : ℝ)^4127 ≤ (43499257025957/100000000000000 : ℝ)^3103 := by
    have hnat : (5347890331 : ℕ)^4127*100000000000000^3103 ≤ 43499257025957^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347890331 10000000000 43499257025957 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456562289/2000000000 : ℝ)^4127 ≤ (14020486623547/100000000000000 : ℝ)^3103 := by
    have hnat : (456562289 : ℕ)^4127*100000000000000^3103 ≤ 14020486623547^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456562289 2000000000 14020486623547 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253420053/10000000000 : ℝ)^4127 ≤ (2124012816539/5000000000000 : ℝ)^3103 := by
    have hnat : (5253420053 : ℕ)^4127*5000000000000^3103 ≤ 2124012816539^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253420053 10000000000 2124012816539 5000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347890331/10000000000 : ℝ), (-456562289/2000000000 : ℝ), (5253420053/10000000000 : ℝ)] ![(43499257025957/100000000000000 : ℝ), (14020486623547/100000000000000 : ℝ), (2124012816539/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347890331/10000000000 : ℝ)|^4127 ≤ (43499257025957/100000000000000 : ℝ)^3103
        have hw : |(5347890331/10000000000 : ℝ)|=(5347890331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456562289/2000000000 : ℝ)|^4127 ≤ (14020486623547/100000000000000 : ℝ)^3103
        have hw : |(-456562289/2000000000 : ℝ)|=(456562289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253420053/10000000000 : ℝ)|^4127 ≤ (2124012816539/5000000000000 : ℝ)^3103
        have hw : |(5253420053/10000000000 : ℝ)|=(5253420053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s4_2 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347889779/10000000000 : ℝ)*x 0 + (525342057/1000000000 : ℝ)*x 1 + (-456562299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347889779/10000000000 : ℝ)^4127 ≤ (43499251054351/100000000000000 : ℝ)^3103 := by
    have hnat : (5347889779 : ℕ)^4127*100000000000000^3103 ≤ 43499251054351^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347889779 10000000000 43499251054351 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525342057/1000000000 : ℝ)^4127 ≤ (5310032736369/12500000000000 : ℝ)^3103 := by
    have hnat : (525342057 : ℕ)^4127*12500000000000^3103 ≤ 5310032736369^3103*1000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525342057 1000000000 5310032736369 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456562299/2000000000 : ℝ)^4127 ≤ (560819481279/4000000000000 : ℝ)^3103 := by
    have hnat : (456562299 : ℕ)^4127*4000000000000^3103 ≤ 560819481279^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456562299 2000000000 560819481279 4000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347889779/10000000000 : ℝ), (525342057/1000000000 : ℝ), (-456562299/2000000000 : ℝ)] ![(43499251054351/100000000000000 : ℝ), (5310032736369/12500000000000 : ℝ), (560819481279/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347889779/10000000000 : ℝ)|^4127 ≤ (43499251054351/100000000000000 : ℝ)^3103
        have hw : |(5347889779/10000000000 : ℝ)|=(5347889779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525342057/1000000000 : ℝ)|^4127 ≤ (5310032736369/12500000000000 : ℝ)^3103
        have hw : |(525342057/1000000000 : ℝ)|=(525342057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456562299/2000000000 : ℝ)|^4127 ≤ (560819481279/4000000000000 : ℝ)^3103
        have hw : |(-456562299/2000000000 : ℝ)|=(456562299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s4_3 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375585647/10000000000 : ℝ)*x 0 + (2114356479/5000000000 : ℝ)*x 1 + (1131908487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375585647/10000000000 : ℝ)^4127 ≤ (8327544906369/25000000000000 : ℝ)^3103 := by
    have hnat : (4375585647 : ℕ)^4127*25000000000000^3103 ≤ 8327544906369^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375585647 10000000000 8327544906369 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114356479/5000000000 : ℝ)^4127 ≤ (15915698901819/50000000000000 : ℝ)^3103 := by
    have hnat : (2114356479 : ℕ)^4127*50000000000000^3103 ≤ 15915698901819^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114356479 5000000000 15915698901819 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131908487/2500000000 : ℝ)^4127 ≤ (34858422549713/100000000000000 : ℝ)^3103 := by
    have hnat : (1131908487 : ℕ)^4127*100000000000000^3103 ≤ 34858422549713^3103*2500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131908487 2500000000 34858422549713 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375585647/10000000000 : ℝ), (2114356479/5000000000 : ℝ), (1131908487/2500000000 : ℝ)] ![(8327544906369/25000000000000 : ℝ), (15915698901819/50000000000000 : ℝ), (34858422549713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375585647/10000000000 : ℝ)|^4127 ≤ (8327544906369/25000000000000 : ℝ)^3103
        have hw : |(4375585647/10000000000 : ℝ)|=(4375585647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114356479/5000000000 : ℝ)|^4127 ≤ (15915698901819/50000000000000 : ℝ)^3103
        have hw : |(2114356479/5000000000 : ℝ)|=(2114356479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131908487/2500000000 : ℝ)|^4127 ≤ (34858422549713/100000000000000 : ℝ)^3103
        have hw : |(1131908487/2500000000 : ℝ)|=(1131908487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s4_4 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102580559/5000000000 : ℝ)*x 0 + (1050773643/2000000000 : ℝ)*x 1 + (216225713/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102580559/5000000000 : ℝ)^4127 ≤ (13389782362909/100000000000000 : ℝ)^3103 := by
    have hnat : (1102580559 : ℕ)^4127*100000000000000^3103 ≤ 13389782362909^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102580559 5000000000 13389782362909 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050773643/2000000000 : ℝ)^4127 ≤ (531063452997/1250000000000 : ℝ)^3103 := by
    have hnat : (1050773643 : ℕ)^4127*1250000000000^3103 ≤ 531063452997^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050773643 2000000000 531063452997 1250000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216225713/400000000 : ℝ)^4127 ≤ (11031285345763/25000000000000 : ℝ)^3103 := by
    have hnat : (216225713 : ℕ)^4127*25000000000000^3103 ≤ 11031285345763^3103*400000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216225713 400000000 11031285345763 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102580559/5000000000 : ℝ), (1050773643/2000000000 : ℝ), (216225713/400000000 : ℝ)] ![(13389782362909/100000000000000 : ℝ), (531063452997/1250000000000 : ℝ), (11031285345763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102580559/5000000000 : ℝ)|^4127 ≤ (13389782362909/100000000000000 : ℝ)^3103
        have hw : |(-1102580559/5000000000 : ℝ)|=(1102580559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050773643/2000000000 : ℝ)|^4127 ≤ (531063452997/1250000000000 : ℝ)^3103
        have hw : |(1050773643/2000000000 : ℝ)|=(1050773643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216225713/400000000 : ℝ)|^4127 ≤ (11031285345763/25000000000000 : ℝ)^3103
        have hw : |(216225713/400000000 : ℝ)|=(216225713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s4_5 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309452479/10000000000 : ℝ)*x 0 + (-2130588313/10000000000 : ℝ)*x 1 + (5405642839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309452479/10000000000 : ℝ)^4127 ≤ (2154196271803/5000000000000 : ℝ)^3103 := by
    have hnat : (5309452479 : ℕ)^4127*5000000000000^3103 ≤ 2154196271803^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309452479 10000000000 2154196271803 5000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130588313/10000000000 : ℝ)^4127 ≤ (12790933019963/100000000000000 : ℝ)^3103 := by
    have hnat : (2130588313 : ℕ)^4127*100000000000000^3103 ≤ 12790933019963^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130588313 10000000000 12790933019963 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405642839/10000000000 : ℝ)^4127 ≤ (44125141535043/100000000000000 : ℝ)^3103 := by
    have hnat : (5405642839 : ℕ)^4127*100000000000000^3103 ≤ 44125141535043^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405642839 10000000000 44125141535043 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309452479/10000000000 : ℝ), (-2130588313/10000000000 : ℝ), (5405642839/10000000000 : ℝ)] ![(2154196271803/5000000000000 : ℝ), (12790933019963/100000000000000 : ℝ), (44125141535043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309452479/10000000000 : ℝ)|^4127 ≤ (2154196271803/5000000000000 : ℝ)^3103
        have hw : |(5309452479/10000000000 : ℝ)|=(5309452479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130588313/10000000000 : ℝ)|^4127 ≤ (12790933019963/100000000000000 : ℝ)^3103
        have hw : |(-2130588313/10000000000 : ℝ)|=(2130588313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405642839/10000000000 : ℝ)|^4127 ≤ (44125141535043/100000000000000 : ℝ)^3103
        have hw : |(5405642839/10000000000 : ℝ)|=(5405642839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s4_6 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309452471/10000000000 : ℝ)*x 0 + (5405642811/10000000000 : ℝ)*x 1 + (-1065294181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309452471/10000000000 : ℝ)^4127 ≤ (43083925349721/100000000000000 : ℝ)^3103 := by
    have hnat : (5309452471 : ℕ)^4127*100000000000000^3103 ≤ 43083925349721^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309452471 10000000000 43083925349721 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405642811/10000000000 : ℝ)^4127 ≤ (2206257061553/5000000000000 : ℝ)^3103 := by
    have hnat : (5405642811 : ℕ)^4127*5000000000000^3103 ≤ 2206257061553^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405642811 10000000000 2206257061553 5000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065294181/5000000000 : ℝ)^4127 ≤ (12790933411211/100000000000000 : ℝ)^3103 := by
    have hnat : (1065294181 : ℕ)^4127*100000000000000^3103 ≤ 12790933411211^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065294181 5000000000 12790933411211 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309452471/10000000000 : ℝ), (5405642811/10000000000 : ℝ), (-1065294181/5000000000 : ℝ)] ![(43083925349721/100000000000000 : ℝ), (2206257061553/5000000000000 : ℝ), (12790933411211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309452471/10000000000 : ℝ)|^4127 ≤ (43083925349721/100000000000000 : ℝ)^3103
        have hw : |(5309452471/10000000000 : ℝ)|=(5309452471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405642811/10000000000 : ℝ)|^4127 ≤ (2206257061553/5000000000000 : ℝ)^3103
        have hw : |(5405642811/10000000000 : ℝ)|=(5405642811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065294181/5000000000 : ℝ)|^4127 ≤ (12790933411211/100000000000000 : ℝ)^3103
        have hw : |(-1065294181/5000000000 : ℝ)|=(1065294181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s4_7 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375601671/10000000000 : ℝ)*x 0 + (4526756193/10000000000 : ℝ)*x 1 + (4229594459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375601671/10000000000 : ℝ)^4127 ≤ (16655170933997/50000000000000 : ℝ)^3103 := by
    have hnat : (4375601671 : ℕ)^4127*50000000000000^3103 ≤ 16655170933997^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375601671 10000000000 16655170933997 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526756193/10000000000 : ℝ)^4127 ≤ (8712358712599/25000000000000 : ℝ)^3103 := by
    have hnat : (4526756193 : ℕ)^4127*25000000000000^3103 ≤ 8712358712599^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526756193 10000000000 8712358712599 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229594459/10000000000 : ℝ)^4127 ≤ (3184022327567/10000000000000 : ℝ)^3103 := by
    have hnat : (4229594459 : ℕ)^4127*10000000000000^3103 ≤ 3184022327567^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229594459 10000000000 3184022327567 10000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375601671/10000000000 : ℝ), (4526756193/10000000000 : ℝ), (4229594459/10000000000 : ℝ)] ![(16655170933997/50000000000000 : ℝ), (8712358712599/25000000000000 : ℝ), (3184022327567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375601671/10000000000 : ℝ)|^4127 ≤ (16655170933997/50000000000000 : ℝ)^3103
        have hw : |(4375601671/10000000000 : ℝ)|=(4375601671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526756193/10000000000 : ℝ)|^4127 ≤ (8712358712599/25000000000000 : ℝ)^3103
        have hw : |(4526756193/10000000000 : ℝ)|=(4526756193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229594459/10000000000 : ℝ)|^4127 ≤ (3184022327567/10000000000000 : ℝ)^3103
        have hw : |(4229594459/10000000000 : ℝ)|=(4229594459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1061_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3561/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10379/100000 : ℝ) ^ (8253/2048 : ℝ) ≤ (10847210946707249/100000000000000000000 : ℝ) := by
    have hpowers : (10379/100000 : ℝ)^8253 ≤ (10847210946707249/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10379 : ℕ)^8253*100000000000000000000^2048 ≤ 10847210946707249^2048*100000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10379 100000 10847210946707249 100000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10379/100000 : ℝ)) (X := (10847210946707249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14913/100000 : ℝ) ^ (8253/2048 : ℝ) ≤ (11683812665878019/25000000000000000000 : ℝ) := by
    have hpowers : (14913/100000 : ℝ)^8253 ≤ (11683812665878019/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14913 : ℕ)^8253*25000000000000000000^2048 ≤ 11683812665878019^2048*100000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14913 100000 11683812665878019 25000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14913/100000 : ℝ)) (X := (11683812665878019/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010847210946707249/50000000000000000000 : ℝ) ≤ (5000269153962287/5000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50010847210946707249/50000000000000000000 : ℝ)^2048 ≤ (5000269153962287/5000000000000000 : ℝ)^8253 := by
      have hnat : (50010847210946707249 : ℕ)^2048*5000000000000000^8253 ≤ 5000269153962287^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010847210946707249 50000000000000000000 5000269153962287 5000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269153962287/5000000000000000 : ℝ)) (X := (50010847210946707249/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002303298464408773/4000000000000000000 : ℝ) ≤ (1250178576521169/1250000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (4002303298464408773/4000000000000000000 : ℝ)^2048 ≤ (1250178576521169/1250000000000000 : ℝ)^8253 := by
      have hnat : (4002303298464408773 : ℕ)^2048*1250000000000000^8253 ≤ 1250178576521169^8253*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002303298464408773 4000000000000000000 1250178576521169 1250000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250178576521169/1250000000000000 : ℝ)) (X := (4002303298464408773/4000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511683812665878019/12500000000000000000 : ℝ) ≤ (1000231891641413/1000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (12511683812665878019/12500000000000000000 : ℝ)^2048 ≤ (1000231891641413/1000000000000000 : ℝ)^8253 := by
      have hnat : (12511683812665878019 : ℕ)^2048*1000000000000000^8253 ≤ 1000231891641413^8253*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511683812665878019 12500000000000000000 1000231891641413 1000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000231891641413/1000000000000000 : ℝ)) (X := (12511683812665878019/12500000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10847210946707249/100000000000000000000 : ℝ) ≤ ((5665494969077114599/5667500000000000000 : ℝ)+2*(445152122389/226700000000000 : ℝ)*(10379/100000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (5665494969077114599/5667500000000000000 : ℝ)+2*(445152122389/226700000000000 : ℝ)*(10379/100000 : ℝ)=(5000269153962287/5000000000000000 : ℝ) by norm_num, show 1+2*(10847210946707249/100000000000000000000 : ℝ)=(50010847210946707249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11683812665878019/25000000000000000000 : ℝ)+(10847210946707249/100000000000000000000 : ℝ) ≤ ((5665494969077114599/5667500000000000000 : ℝ)+(445152122389/226700000000000 : ℝ)*((14913/100000 : ℝ)+(10379/100000 : ℝ)))^(8253/2048 : ℝ) := by
    rw [show (5665494969077114599/5667500000000000000 : ℝ)+(445152122389/226700000000000 : ℝ)*((14913/100000 : ℝ)+(10379/100000 : ℝ))=(1250178576521169/1250000000000000 : ℝ) by norm_num, show 1+(11683812665878019/25000000000000000000 : ℝ)+(10847210946707249/100000000000000000000 : ℝ)=(4002303298464408773/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11683812665878019/25000000000000000000 : ℝ) ≤ ((5665494969077114599/5667500000000000000 : ℝ)+2*(445152122389/226700000000000 : ℝ)*(14913/100000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (5665494969077114599/5667500000000000000 : ℝ)+2*(445152122389/226700000000000 : ℝ)*(14913/100000 : ℝ)=(1000231891641413/1000000000000000 : ℝ) by norm_num, show 1+2*(11683812665878019/25000000000000000000 : ℝ)=(12511683812665878019/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5665494969077114599/5667500000000000000 : ℝ)*(X 1 0+X 2 0)+(445152122389/226700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (10379/100000 : ℝ)) (hi := (14913/100000 : ℝ)) (c := (5665494969077114599/5667500000000000000 : ℝ)) (alpha := (445152122389/226700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5665494969077114599/5667500000000000000 : ℝ)*(X 0 1+X 2 1)+(445152122389/226700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (10379/100000 : ℝ)) (hi := (14913/100000 : ℝ)) (c := (5665494969077114599/5667500000000000000 : ℝ)) (alpha := (445152122389/226700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5665494969077114599/5667500000000000000 : ℝ)*(X 0 2+X 1 2)+(445152122389/226700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (10379/100000 : ℝ)) (hi := (14913/100000 : ℝ)) (c := (5665494969077114599/5667500000000000000 : ℝ)) (alpha := (445152122389/226700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-441030637/2000000000 : ℝ)*X 0 0+(5406093493/10000000000 : ℝ)*X 0 1+(1050683847/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347890331/10000000000 : ℝ)*X 1 0+(-456562289/2000000000 : ℝ)*X 1 1+(5253420053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347889779/10000000000 : ℝ)*X 2 0+(525342057/1000000000 : ℝ)*X 2 1+(-456562299/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375585647/10000000000 : ℝ)*X 0 0+(2114356479/5000000000 : ℝ)*X 0 1+(1131908487/2500000000 : ℝ)*X 0 2+(4375585647/10000000000 : ℝ)*X 1 0+(2114356479/5000000000 : ℝ)*X 1 1+(1131908487/2500000000 : ℝ)*X 1 2+(4375585647/10000000000 : ℝ)*X 2 0+(2114356479/5000000000 : ℝ)*X 2 1+(1131908487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1102580559/5000000000 : ℝ)*X 0 0+(1050773643/2000000000 : ℝ)*X 0 1+(216225713/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309452479/10000000000 : ℝ)*X 1 0+(-2130588313/10000000000 : ℝ)*X 1 1+(5405642839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309452471/10000000000 : ℝ)*X 2 0+(5405642811/10000000000 : ℝ)*X 2 1+(-1065294181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375601671/10000000000 : ℝ)*X 0 0+(4526756193/10000000000 : ℝ)*X 0 1+(4229594459/10000000000 : ℝ)*X 0 2+(4375601671/10000000000 : ℝ)*X 1 0+(4526756193/10000000000 : ℝ)*X 1 1+(4229594459/10000000000 : ℝ)*X 1 2+(4375601671/10000000000 : ℝ)*X 2 0+(4526756193/10000000000 : ℝ)*X 2 1+(4229594459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7480868552153638116940641/708437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (94948987/6250000000000 : ℝ)*(base19) + (755677821/100000000000000 : ℝ)*(base23) + (464558633/100000000000000 : ℝ)*(upper3) + (23376997/50000000000000 : ℝ)*(upper4) + (201486393/100000000000000 : ℝ)*(upper5) + (12369266575439/250000000000 : ℝ)*(major0) + (12369266575439/250000000000 : ℝ)*(major1) + (12369266575439/250000000000 : ℝ)*(major2) + (163749001635493/2500000000000 : ℝ)*(sp0) + (1637502649080399/25000000000000 : ℝ)*(sp1) + (3275005679913783/50000000000000 : ℝ)*(sp2) + (66907644189621/2000000000000 : ℝ)*(sp3) + (13012521417/25000000000000 : ℝ)*(sp4) + (4645843911/25000000000000 : ℝ)*(sp7) + (1672700396428347/50000000000000 : ℝ)*(f.failure) + (1637503028876347/25000000000000 : ℝ)*(f.sum) + (608498690653/226700000000000000000000000 : ℝ)*base65 + (12254086424693539/1416875000000000000000000000000 : ℝ)*base68 + (10391398115886039/1416875000000000000000000000000 : ℝ)*base70 + (20135375652897289/1416875000000000000000000000000 : ℝ)*base72 + (77111553961/566750000000000000000000000 : ℝ)*base74 + (14936050590196039/1416875000000000000000000000000 : ℝ)*base76 + (2536098410011461/1416875000000000000000000000000 : ℝ)*base77 + (19535843503868539/1416875000000000000000000000000 : ℝ)*base80 + (1801486219569/1133500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (9895993/5000000000000000000000 : ℝ)*base90 + (9895993/5000000000000000000000 : ℝ)*base92 + (9895993/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (449111978111280286691891577/70843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10820507/781250000000 : ℝ)*(base19) + (769944419/50000000000000 : ℝ)*(base23) + (31266871/25000000000000 : ℝ)*(upper3) + (21754961/25000000000000 : ℝ)*(lower4) + (8639281/5000000000000 : ℝ)*(upper5) + (2488471626064009/50000000000000 : ℝ)*(major0) + (2488471626064009/50000000000000 : ℝ)*(major1) + (2488471626064009/50000000000000 : ℝ)*(major2) + (34192425333/100000000000000 : ℝ)*(sp1) + (17158295811/50000000000000 : ℝ)*(sp2) + (3294358552617527/50000000000000 : ℝ)*(sp4) + (823585190973103/12500000000000 : ℝ)*(sp5) + (3294340624377297/50000000000000 : ℝ)*(sp6) + (1682584593852619/50000000000000 : ℝ)*(sp7) + (1682584593852619/50000000000000 : ℝ)*(f.failure) + (3294358552617527/50000000000000 : ℝ)*(f.sum) + (294779289611/88554687500000000000000000 : ℝ)*base66 + (851260277158892391/283375000000000000000000000000000 : ℝ)*base67 + (1093541297881892391/283375000000000000000000000000000 : ℝ)*base69 + (1417007392347517391/283375000000000000000000000000000 : ℝ)*base71 + (12315466607607/11335000000000000000000000000 : ℝ)*base73 + (1410272245863767391/283375000000000000000000000000000 : ℝ)*base75 + (2198782514356142391/283375000000000000000000000000000 : ℝ)*base77 + (2761595185127107609/283375000000000000000000000000000 : ℝ)*base80 + (18642144293769/5667500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (14099561/5000000000000000000000 : ℝ)*base90 + (14099561/5000000000000000000000 : ℝ)*base92 + (14099561/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1061_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1061_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1061_s5_0 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205996021/10000000000 : ℝ)*x 0 + (5397143227/10000000000 : ℝ)*x 1 + (52618169/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205996021/10000000000 : ℝ)^4127 ≤ (13396525298863/100000000000000 : ℝ)^3103 := by
    have hnat : (2205996021 : ℕ)^4127*100000000000000^3103 ≤ 13396525298863^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205996021 10000000000 13396525298863 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397143227/10000000000 : ℝ)^4127 ≤ (44032889101841/100000000000000 : ℝ)^3103 := by
    have hnat : (5397143227 : ℕ)^4127*100000000000000^3103 ≤ 44032889101841^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397143227 10000000000 44032889101841 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52618169/100000000 : ℝ)^4127 ≤ (42570585583133/100000000000000 : ℝ)^3103 := by
    have hnat : (52618169 : ℕ)^4127*100000000000000^3103 ≤ 42570585583133^3103*100000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52618169 100000000 42570585583133 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205996021/10000000000 : ℝ), (5397143227/10000000000 : ℝ), (52618169/100000000 : ℝ)] ![(13396525298863/100000000000000 : ℝ), (44032889101841/100000000000000 : ℝ), (42570585583133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205996021/10000000000 : ℝ)|^4127 ≤ (13396525298863/100000000000000 : ℝ)^3103
        have hw : |(-2205996021/10000000000 : ℝ)|=(2205996021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397143227/10000000000 : ℝ)|^4127 ≤ (44032889101841/100000000000000 : ℝ)^3103
        have hw : |(5397143227/10000000000 : ℝ)|=(5397143227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52618169/100000000 : ℝ)|^4127 ≤ (42570585583133/100000000000000 : ℝ)^3103
        have hw : |(52618169/100000000 : ℝ)|=(52618169/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s5_1 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069132631/2000000000 : ℝ)*x 0 + (-227469793/1000000000 : ℝ)*x 1 + (1052363377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069132631/2000000000 : ℝ)^4127 ≤ (8695032962183/20000000000000 : ℝ)^3103 := by
    have hnat : (1069132631 : ℕ)^4127*20000000000000^3103 ≤ 8695032962183^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069132631 2000000000 8695032962183 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227469793/1000000000 : ℝ)^4127 ≤ (1744281218927/12500000000000 : ℝ)^3103 := by
    have hnat : (227469793 : ℕ)^4127*12500000000000^3103 ≤ 1744281218927^3103*1000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227469793 1000000000 1744281218927 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052363377/2000000000 : ℝ)^4127 ≤ (42570585421727/100000000000000 : ℝ)^3103 := by
    have hnat : (1052363377 : ℕ)^4127*100000000000000^3103 ≤ 42570585421727^3103*2000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052363377 2000000000 42570585421727 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069132631/2000000000 : ℝ), (-227469793/1000000000 : ℝ), (1052363377/2000000000 : ℝ)] ![(8695032962183/20000000000000 : ℝ), (1744281218927/12500000000000 : ℝ), (42570585421727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069132631/2000000000 : ℝ)|^4127 ≤ (8695032962183/20000000000000 : ℝ)^3103
        have hw : |(1069132631/2000000000 : ℝ)|=(1069132631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227469793/1000000000 : ℝ)|^4127 ≤ (1744281218927/12500000000000 : ℝ)^3103
        have hw : |(-227469793/1000000000 : ℝ)|=(227469793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052363377/2000000000 : ℝ)|^4127 ≤ (42570585421727/100000000000000 : ℝ)^3103
        have hw : |(1052363377/2000000000 : ℝ)|=(1052363377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s5_2 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53456631/100000000 : ℝ)*x 0 + (328863557/625000000 : ℝ)*x 1 + (-2274697967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53456631/100000000 : ℝ)^4127 ≤ (5434395527/12500000000 : ℝ)^3103 := by
    have hnat : (53456631 : ℕ)^4127*12500000000^3103 ≤ 5434395527^3103*100000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53456631 100000000 5434395527 12500000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328863557/625000000 : ℝ)^4127 ≤ (42570585712257/100000000000000 : ℝ)^3103 := by
    have hnat : (328863557 : ℕ)^4127*100000000000000^3103 ≤ 42570585712257^3103*625000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328863557 625000000 42570585712257 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274697967/10000000000 : ℝ)^4127 ≤ (6977125026649/50000000000000 : ℝ)^3103 := by
    have hnat : (2274697967 : ℕ)^4127*50000000000000^3103 ≤ 6977125026649^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274697967 10000000000 6977125026649 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53456631/100000000 : ℝ), (328863557/625000000 : ℝ), (-2274697967/10000000000 : ℝ)] ![(5434395527/12500000000 : ℝ), (42570585712257/100000000000000 : ℝ), (6977125026649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53456631/100000000 : ℝ)|^4127 ≤ (5434395527/12500000000 : ℝ)^3103
        have hw : |(53456631/100000000 : ℝ)|=(53456631/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328863557/625000000 : ℝ)|^4127 ≤ (42570585712257/100000000000000 : ℝ)^3103
        have hw : |(328863557/625000000 : ℝ)|=(328863557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2274697967/10000000000 : ℝ)|^4127 ≤ (6977125026649/50000000000000 : ℝ)^3103
        have hw : |(-2274697967/10000000000 : ℝ)|=(2274697967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s5_3 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4376075321/10000000000 : ℝ)*x 0 + (4245630253/10000000000 : ℝ)*x 1 + (1127647/2500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376075321/10000000000 : ℝ)^4127 ≤ (6663027529709/20000000000000 : ℝ)^3103 := by
    have hnat : (4376075321 : ℕ)^4127*20000000000000^3103 ≤ 6663027529709^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376075321 10000000000 6663027529709 20000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245630253/10000000000 : ℝ)^4127 ≤ (32000877410453/100000000000000 : ℝ)^3103 := by
    have hnat : (4245630253 : ℕ)^4127*100000000000000^3103 ≤ 32000877410453^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245630253 10000000000 32000877410453 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127647/2500000 : ℝ)^4127 ≤ (17341992460149/50000000000000 : ℝ)^3103 := by
    have hnat : (1127647 : ℕ)^4127*50000000000000^3103 ≤ 17341992460149^3103*2500000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127647 2500000 17341992460149 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376075321/10000000000 : ℝ), (4245630253/10000000000 : ℝ), (1127647/2500000 : ℝ)] ![(6663027529709/20000000000000 : ℝ), (32000877410453/100000000000000 : ℝ), (17341992460149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376075321/10000000000 : ℝ)|^4127 ≤ (6663027529709/20000000000000 : ℝ)^3103
        have hw : |(4376075321/10000000000 : ℝ)|=(4376075321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245630253/10000000000 : ℝ)|^4127 ≤ (32000877410453/100000000000000 : ℝ)^3103
        have hw : |(4245630253/10000000000 : ℝ)|=(4245630253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127647/2500000 : ℝ)|^4127 ≤ (17341992460149/50000000000000 : ℝ)^3103
        have hw : |(1127647/2500000 : ℝ)|=(1127647/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s5_4 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11030009/50000000 : ℝ)*x 0 + (2631084649/5000000000 : ℝ)*x 1 + (269839473/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11030009/50000000 : ℝ)^4127 ≤ (6698285987399/50000000000000 : ℝ)^3103 := by
    have hnat : (11030009 : ℕ)^4127*50000000000000^3103 ≤ 6698285987399^3103*50000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11030009 50000000 6698285987399 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631084649/5000000000 : ℝ)^4127 ≤ (21287188776249/50000000000000 : ℝ)^3103 := by
    have hnat : (2631084649 : ℕ)^4127*50000000000000^3103 ≤ 21287188776249^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631084649 5000000000 21287188776249 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269839473/500000000 : ℝ)^4127 ≤ (44029050451513/100000000000000 : ℝ)^3103 := by
    have hnat : (269839473 : ℕ)^4127*100000000000000^3103 ≤ 44029050451513^3103*500000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269839473 500000000 44029050451513 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11030009/50000000 : ℝ), (2631084649/5000000000 : ℝ), (269839473/500000000 : ℝ)] ![(6698285987399/50000000000000 : ℝ), (21287188776249/50000000000000 : ℝ), (44029050451513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11030009/50000000 : ℝ)|^4127 ≤ (6698285987399/50000000000000 : ℝ)^3103
        have hw : |(-11030009/50000000 : ℝ)|=(11030009/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631084649/5000000000 : ℝ)|^4127 ≤ (21287188776249/50000000000000 : ℝ)^3103
        have hw : |(2631084649/5000000000 : ℝ)|=(2631084649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269839473/500000000 : ℝ)|^4127 ≤ (44029050451513/100000000000000 : ℝ)^3103
        have hw : |(269839473/500000000 : ℝ)|=(269839473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s5_5 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655795579/5000000000 : ℝ)*x 0 + (-66866419/312500000 : ℝ)*x 1 + (2698394733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655795579/5000000000 : ℝ)^4127 ≤ (5388376057401/12500000000000 : ℝ)^3103 := by
    have hnat : (2655795579 : ℕ)^4127*12500000000000^3103 ≤ 5388376057401^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655795579 5000000000 5388376057401 12500000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66866419/312500000 : ℝ)^4127 ≤ (12863941016161/100000000000000 : ℝ)^3103 := by
    have hnat : (66866419 : ℕ)^4127*100000000000000^3103 ≤ 12863941016161^3103*312500000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66866419 312500000 12863941016161 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698394733/5000000000 : ℝ)^4127 ≤ (44029050516617/100000000000000 : ℝ)^3103 := by
    have hnat : (2698394733 : ℕ)^4127*100000000000000^3103 ≤ 44029050516617^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698394733 5000000000 44029050516617 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655795579/5000000000 : ℝ), (-66866419/312500000 : ℝ), (2698394733/5000000000 : ℝ)] ![(5388376057401/12500000000000 : ℝ), (12863941016161/100000000000000 : ℝ), (44029050516617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655795579/5000000000 : ℝ)|^4127 ≤ (5388376057401/12500000000000 : ℝ)^3103
        have hw : |(2655795579/5000000000 : ℝ)|=(2655795579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66866419/312500000 : ℝ)|^4127 ≤ (12863941016161/100000000000000 : ℝ)^3103
        have hw : |(-66866419/312500000 : ℝ)|=(66866419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698394733/5000000000 : ℝ)|^4127 ≤ (44029050516617/100000000000000 : ℝ)^3103
        have hw : |(2698394733/5000000000 : ℝ)|=(2698394733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s5_6 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655795573/5000000000 : ℝ)*x 0 + (5396789513/10000000000 : ℝ)*x 1 + (-2139725359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655795573/5000000000 : ℝ)^4127 ≤ (21553504164841/50000000000000 : ℝ)^3103 := by
    have hnat : (2655795573 : ℕ)^4127*50000000000000^3103 ≤ 21553504164841^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655795573 5000000000 21553504164841 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396789513/10000000000 : ℝ)^4127 ≤ (44029051026599/100000000000000 : ℝ)^3103 := by
    have hnat : (5396789513 : ℕ)^4127*100000000000000^3103 ≤ 44029051026599^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396789513 10000000000 44029051026599 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139725359/10000000000 : ℝ)^4127 ≤ (12863940624361/100000000000000 : ℝ)^3103 := by
    have hnat : (2139725359 : ℕ)^4127*100000000000000^3103 ≤ 12863940624361^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139725359 10000000000 12863940624361 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655795573/5000000000 : ℝ), (5396789513/10000000000 : ℝ), (-2139725359/10000000000 : ℝ)] ![(21553504164841/50000000000000 : ℝ), (44029051026599/100000000000000 : ℝ), (12863940624361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655795573/5000000000 : ℝ)|^4127 ≤ (21553504164841/50000000000000 : ℝ)^3103
        have hw : |(2655795573/5000000000 : ℝ)|=(2655795573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396789513/10000000000 : ℝ)|^4127 ≤ (44029051026599/100000000000000 : ℝ)^3103
        have hw : |(5396789513/10000000000 : ℝ)|=(5396789513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139725359/10000000000 : ℝ)|^4127 ≤ (12863940624361/100000000000000 : ℝ)^3103
        have hw : |(-2139725359/10000000000 : ℝ)|=(2139725359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1061_s5_7 (p : ℝ) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4376086533/10000000000 : ℝ)*x 0 + (2254948963/5000000000 : ℝ)*x 1 + (4246322891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376086533/10000000000 : ℝ)^4127 ≤ (33315251173879/100000000000000 : ℝ)^3103 := by
    have hnat : (4376086533 : ℕ)^4127*100000000000000^3103 ≤ 33315251173879^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376086533 10000000000 33315251173879 100000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254948963/5000000000 : ℝ)^4127 ≤ (17338463853669/50000000000000 : ℝ)^3103 := by
    have hnat : (2254948963 : ℕ)^4127*50000000000000^3103 ≤ 17338463853669^3103*5000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254948963 5000000000 17338463853669 50000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246322891/10000000000 : ℝ)^4127 ≤ (8001955275477/25000000000000 : ℝ)^3103 := by
    have hnat : (4246322891 : ℕ)^4127*25000000000000^3103 ≤ 8001955275477^3103*10000000000^4127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246322891 10000000000 8001955275477 25000000000000 4127 3103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4127/1024 : ℝ)) 4127 3103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376086533/10000000000 : ℝ), (2254948963/5000000000 : ℝ), (4246322891/10000000000 : ℝ)] ![(33315251173879/100000000000000 : ℝ), (17338463853669/50000000000000 : ℝ), (8001955275477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376086533/10000000000 : ℝ)|^4127 ≤ (33315251173879/100000000000000 : ℝ)^3103
        have hw : |(4376086533/10000000000 : ℝ)|=(4376086533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254948963/5000000000 : ℝ)|^4127 ≤ (17338463853669/50000000000000 : ℝ)^3103
        have hw : |(2254948963/5000000000 : ℝ)|=(2254948963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246322891/10000000000 : ℝ)|^4127 ≤ (8001955275477/25000000000000 : ℝ)^3103
        have hw : |(4246322891/10000000000 : ℝ)|=(4246322891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1061_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1119/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11011/100000 : ℝ) ^ (8253/2048 : ℝ) ≤ (13764730443286373/100000000000000000000 : ℝ) := by
    have hpowers : (11011/100000 : ℝ)^8253 ≤ (13764730443286373/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11011 : ℕ)^8253*100000000000000000000^2048 ≤ 13764730443286373^2048*100000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11011 100000 13764730443286373 100000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11011/100000 : ℝ)) (X := (13764730443286373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3561/25000 : ℝ) ^ (8253/2048 : ℝ) ≤ (38843526891730161/100000000000000000000 : ℝ) := by
    have hpowers : (3561/25000 : ℝ)^8253 ≤ (38843526891730161/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3561 : ℕ)^8253*100000000000000000000^2048 ≤ 38843526891730161^2048*25000^8253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3561 25000 38843526891730161 100000000000000000000 8253 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3561/25000 : ℝ)) (X := (38843526891730161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013764730443286373/50000000000000000000 : ℝ) ≤ (2000136615781031/2000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50013764730443286373/50000000000000000000 : ℝ)^2048 ≤ (2000136615781031/2000000000000000 : ℝ)^8253 := by
      have hnat : (50013764730443286373 : ℕ)^2048*2000000000000000^8253 ≤ 2000136615781031^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013764730443286373 50000000000000000000 2000136615781031 2000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136615781031/2000000000000000 : ℝ)) (X := (50013764730443286373/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026304128667508267/50000000000000000000 : ℝ) ≤ (5000652613654483/5000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50026304128667508267/50000000000000000000 : ℝ)^2048 ≤ (5000652613654483/5000000000000000 : ℝ)^8253 := by
      have hnat : (50026304128667508267 : ℕ)^2048*5000000000000000^8253 ≤ 5000652613654483^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026304128667508267 50000000000000000000 5000652613654483 5000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000652613654483/5000000000000000 : ℝ)) (X := (50026304128667508267/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038843526891730161/50000000000000000000 : ℝ) ≤ (10001927375712777/10000000000000000 : ℝ) ^ (8253/2048 : ℝ) := by
    have hpowers : (50038843526891730161/50000000000000000000 : ℝ)^2048 ≤ (10001927375712777/10000000000000000 : ℝ)^8253 := by
      have hnat : (50038843526891730161 : ℕ)^2048*10000000000000000^8253 ≤ 10001927375712777^8253*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038843526891730161 50000000000000000000 10001927375712777 10000000000000000 2048 8253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001927375712777/10000000000000000 : ℝ)) (X := (50038843526891730161/50000000000000000000 : ℝ)) (by norm_num) 8253 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13764730443286373/100000000000000000000 : ℝ) ≤ ((32318507441951640273/32330000000000000000 : ℝ)+2*(622148403811/323300000000000 : ℝ)*(11011/100000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (32318507441951640273/32330000000000000000 : ℝ)+2*(622148403811/323300000000000 : ℝ)*(11011/100000 : ℝ)=(2000136615781031/2000000000000000 : ℝ) by norm_num, show 1+2*(13764730443286373/100000000000000000000 : ℝ)=(50013764730443286373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38843526891730161/100000000000000000000 : ℝ)+(13764730443286373/100000000000000000000 : ℝ) ≤ ((32318507441951640273/32330000000000000000 : ℝ)+(622148403811/323300000000000 : ℝ)*((3561/25000 : ℝ)+(11011/100000 : ℝ)))^(8253/2048 : ℝ) := by
    rw [show (32318507441951640273/32330000000000000000 : ℝ)+(622148403811/323300000000000 : ℝ)*((3561/25000 : ℝ)+(11011/100000 : ℝ))=(5000652613654483/5000000000000000 : ℝ) by norm_num, show 1+(38843526891730161/100000000000000000000 : ℝ)+(13764730443286373/100000000000000000000 : ℝ)=(50026304128667508267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38843526891730161/100000000000000000000 : ℝ) ≤ ((32318507441951640273/32330000000000000000 : ℝ)+2*(622148403811/323300000000000 : ℝ)*(3561/25000 : ℝ))^(8253/2048 : ℝ) := by
    rw [show (32318507441951640273/32330000000000000000 : ℝ)+2*(622148403811/323300000000000 : ℝ)*(3561/25000 : ℝ)=(10001927375712777/10000000000000000 : ℝ) by norm_num, show 1+2*(38843526891730161/100000000000000000000 : ℝ)=(50038843526891730161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32318507441951640273/32330000000000000000 : ℝ)*(X 1 0+X 2 0)+(622148403811/323300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (32318507441951640273/32330000000000000000 : ℝ)) (alpha := (622148403811/323300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32318507441951640273/32330000000000000000 : ℝ)*(X 0 1+X 2 1)+(622148403811/323300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (32318507441951640273/32330000000000000000 : ℝ)) (alpha := (622148403811/323300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32318507441951640273/32330000000000000000 : ℝ)*(X 0 2+X 1 2)+(622148403811/323300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8253/2048 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (32318507441951640273/32330000000000000000 : ℝ)) (alpha := (622148403811/323300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2205996021/10000000000 : ℝ)*X 0 0+(5397143227/10000000000 : ℝ)*X 0 1+(52618169/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069132631/2000000000 : ℝ)*X 1 0+(-227469793/1000000000 : ℝ)*X 1 1+(1052363377/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53456631/100000000 : ℝ)*X 2 0+(328863557/625000000 : ℝ)*X 2 1+(-2274697967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376075321/10000000000 : ℝ)*X 0 0+(4245630253/10000000000 : ℝ)*X 0 1+(1127647/2500000 : ℝ)*X 0 2+(4376075321/10000000000 : ℝ)*X 1 0+(4245630253/10000000000 : ℝ)*X 1 1+(1127647/2500000 : ℝ)*X 1 2+(4376075321/10000000000 : ℝ)*X 2 0+(4245630253/10000000000 : ℝ)*X 2 1+(1127647/2500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-11030009/50000000 : ℝ)*X 0 0+(2631084649/5000000000 : ℝ)*X 0 1+(269839473/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655795579/5000000000 : ℝ)*X 1 0+(-66866419/312500000 : ℝ)*X 1 1+(2698394733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655795573/5000000000 : ℝ)*X 2 0+(5396789513/10000000000 : ℝ)*X 2 1+(-2139725359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376086533/10000000000 : ℝ)*X 0 0+(2254948963/5000000000 : ℝ)*X 0 1+(4246322891/10000000000 : ℝ)*X 0 2+(4376086533/10000000000 : ℝ)*X 1 0+(2254948963/5000000000 : ℝ)*X 1 1+(4246322891/10000000000 : ℝ)*X 1 2+(4376086533/10000000000 : ℝ)*X 2 0+(2254948963/5000000000 : ℝ)*X 2 1+(4246322891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1061_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (457377549461877467192666007/50515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226007057/12500000000000 : ℝ)*(base19) + (62853391/4000000000000 : ℝ)*(base23) + (85900431/100000000000000 : ℝ)*(lower2) + (130735691/50000000000000 : ℝ)*(upper3) + (1757491/2500000000000 : ℝ)*(upper5) + (348871151034203/6250000000000 : ℝ)*(major0) + (348871151034203/6250000000000 : ℝ)*(major1) + (348871151034203/6250000000000 : ℝ)*(major2) + (73895954901667/1000000000000 : ℝ)*(sp0) + (7389636960122863/100000000000000 : ℝ)*(sp1) + (14432885150087/195312500000 : ℝ)*(sp2) + (1887105037393213/50000000000000 : ℝ)*(sp3) + (43278012619/100000000000000 : ℝ)*(sp4) + (432630043/1562500000000 : ℝ)*(sp7) + (1887118881554589/50000000000000 : ℝ)*(f.failure) + (7389638768179319/100000000000000 : ℝ)*(f.sum) + (13591300760449/8082500000000000000000000000 : ℝ)*base65 + (538855421601192581/202062500000000000000000000000000 : ℝ)*base68 + (1528811999866192581/202062500000000000000000000000000 : ℝ)*base70 + (281329635364119919/202062500000000000000000000000000 : ℝ)*base71 + (4349449918257/4041250000000000000000000000 : ℝ)*base73 + (4431342017147130081/202062500000000000000000000000000 : ℝ)*base76 + (2200990726008067581/202062500000000000000000000000000 : ℝ)*base78 + (3062578819818567581/202062500000000000000000000000000 : ℝ)*base80 + (633350830673/1010312500000000000000000000 : ℝ)*base81 + (34289009/5000000000000000000000 : ℝ)*base89 + (34289009/5000000000000000000000 : ℝ)*base91 + (34289009/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27979774896299077520206251/13250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39364887/10000000000000 : ℝ)*(base19) + (41228237/10000000000000 : ℝ)*(base23) + (4054951/100000000000000 : ℝ)*(upper2) + (73178603/100000000000000 : ℝ)*(upper3) + (1359277/4000000000000 : ℝ)*(upper5) + (5611146451900731/100000000000000 : ℝ)*(major0) + (5611146451900731/100000000000000 : ℝ)*(major1) + (5611146451900731/100000000000000 : ℝ)*(major2) + (8333784771/100000000000000 : ℝ)*(sp1) + (12664738109/100000000000000 : ℝ)*(sp2) + (7428306004334969/100000000000000 : ℝ)*(sp4) + (464268579806333/6250000000000 : ℝ)*(sp5) + (742829292731449/10000000000000 : ℝ)*(sp6) + (474248353634639/12500000000000 : ℝ)*(sp7) + (474248353634639/12500000000000 : ℝ)*(f.failure) + (7428306004334969/100000000000000 : ℝ)*(f.sum) + (49549968048001/16165000000000000000000000000 : ℝ)*base65 + (15062471757159839563/3233000000000000000000000000000000 : ℝ)*base67 + (10037072648354160437/3233000000000000000000000000000000 : ℝ)*base70 + (22320713392776839563/3233000000000000000000000000000000 : ℝ)*base71 + (49738850221271/16165000000000000000000000000 : ℝ)*base73 + (18843825733426839563/3233000000000000000000000000000000 : ℝ)*base75 + (42984390504913839563/3233000000000000000000000000000000 : ℝ)*base77 + (14763545292431839563/3233000000000000000000000000000000 : ℝ)*base79 + (13326777583597/8082500000000000000000000000 : ℝ)*base82 + (13941941/1250000000000000000000 : ℝ)*base90 + (13941941/1250000000000000000000 : ℝ)*base92 + (13941941/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1061_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1061_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1061_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8687/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1061_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1061_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1061_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8253/2048 : ℝ) ≤ p) (hpb : p ≤ (4127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147895781/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8687/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1061_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
