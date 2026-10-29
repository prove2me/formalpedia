-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1747_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:18:01.016058+00:00
-- url     : https://prove2.me/submissions/6e7ba11e-a3b1-4426-8b59-b04c06d896bf

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
theorem support_rectangle_w1747_s0_0 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1191677787/10000000000 : ℝ)*x 0 + (140992683/250000000 : ℝ)*x 1 + (4973278241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1191677787/10000000000 : ℝ)^5727 ≤ (468692302427/6250000000000 : ℝ)^4703 := by
    have hnat : (1191677787 : ℕ)^5727*6250000000000^4703 ≤ 468692302427^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191677787 10000000000 468692302427 6250000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140992683/250000000 : ℝ)^5727 ≤ (49784806360701/100000000000000 : ℝ)^4703 := by
    have hnat : (140992683 : ℕ)^5727*100000000000000^4703 ≤ 49784806360701^4703*250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140992683 250000000 49784806360701 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4973278241/10000000000 : ℝ)^5727 ≤ (2669757299511/6250000000000 : ℝ)^4703 := by
    have hnat : (4973278241 : ℕ)^5727*6250000000000^4703 ≤ 2669757299511^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4973278241 10000000000 2669757299511 6250000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1191677787/10000000000 : ℝ), (140992683/250000000 : ℝ), (4973278241/10000000000 : ℝ)] ![(468692302427/6250000000000 : ℝ), (49784806360701/100000000000000 : ℝ), (2669757299511/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1191677787/10000000000 : ℝ)|^5727 ≤ (468692302427/6250000000000 : ℝ)^4703
        have hw : |(-1191677787/10000000000 : ℝ)|=(1191677787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140992683/250000000 : ℝ)|^5727 ≤ (49784806360701/100000000000000 : ℝ)^4703
        have hw : |(140992683/250000000 : ℝ)|=(140992683/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4973278241/10000000000 : ℝ)|^5727 ≤ (2669757299511/6250000000000 : ℝ)^4703
        have hw : |(4973278241/10000000000 : ℝ)|=(4973278241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s0_1 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687664517/5000000000 : ℝ)*x 0 + (-1549727323/10000000000 : ℝ)*x 1 + (198931143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687664517/5000000000 : ℝ)^5727 ≤ (46957529429823/100000000000000 : ℝ)^4703 := by
    have hnat : (2687664517 : ℕ)^5727*100000000000000^4703 ≤ 46957529429823^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687664517 5000000000 46957529429823 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1549727323/10000000000 : ℝ)^5727 ≤ (516317513559/5000000000000 : ℝ)^4703 := by
    have hnat : (1549727323 : ℕ)^5727*5000000000000^4703 ≤ 516317513559^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549727323 10000000000 516317513559 5000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198931143/400000000 : ℝ)^5727 ≤ (42716120285571/100000000000000 : ℝ)^4703 := by
    have hnat : (198931143 : ℕ)^5727*100000000000000^4703 ≤ 42716120285571^4703*400000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198931143 400000000 42716120285571 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687664517/5000000000 : ℝ), (-1549727323/10000000000 : ℝ), (198931143/400000000 : ℝ)] ![(46957529429823/100000000000000 : ℝ), (516317513559/5000000000000 : ℝ), (42716120285571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687664517/5000000000 : ℝ)|^5727 ≤ (46957529429823/100000000000000 : ℝ)^4703
        have hw : |(2687664517/5000000000 : ℝ)|=(2687664517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1549727323/10000000000 : ℝ)|^5727 ≤ (516317513559/5000000000000 : ℝ)^4703
        have hw : |(-1549727323/10000000000 : ℝ)|=(1549727323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198931143/400000000 : ℝ)|^5727 ≤ (42716120285571/100000000000000 : ℝ)^4703
        have hw : |(198931143/400000000 : ℝ)|=(198931143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s0_2 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343832557/2500000000 : ℝ)*x 0 + (994655577/2000000000 : ℝ)*x 1 + (-1549726647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343832557/2500000000 : ℝ)^5727 ≤ (46957542131373/100000000000000 : ℝ)^4703 := by
    have hnat : (1343832557 : ℕ)^5727*100000000000000^4703 ≤ 46957542131373^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343832557 2500000000 46957542131373 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994655577/2000000000 : ℝ)^5727 ≤ (42716113068677/100000000000000 : ℝ)^4703 := by
    have hnat : (994655577 : ℕ)^5727*100000000000000^4703 ≤ 42716113068677^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994655577 2000000000 42716113068677 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1549726647/10000000000 : ℝ)^5727 ≤ (5163172393003/50000000000000 : ℝ)^4703 := by
    have hnat : (1549726647 : ℕ)^5727*50000000000000^4703 ≤ 5163172393003^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549726647 10000000000 5163172393003 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343832557/2500000000 : ℝ), (994655577/2000000000 : ℝ), (-1549726647/10000000000 : ℝ)] ![(46957542131373/100000000000000 : ℝ), (42716113068677/100000000000000 : ℝ), (5163172393003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343832557/2500000000 : ℝ)|^5727 ≤ (46957542131373/100000000000000 : ℝ)^4703
        have hw : |(1343832557/2500000000 : ℝ)|=(1343832557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994655577/2000000000 : ℝ)|^5727 ≤ (42716113068677/100000000000000 : ℝ)^4703
        have hw : |(994655577/2000000000 : ℝ)|=(994655577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1549726647/10000000000 : ℝ)|^5727 ≤ (5163172393003/50000000000000 : ℝ)^4703
        have hw : |(-1549726647/10000000000 : ℝ)|=(1549726647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s0_3 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (796398429/2000000000 : ℝ)*x 0 + (2981184803/10000000000 : ℝ)*x 1 + (1028799733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796398429/2000000000 : ℝ)^5727 ≤ (3258583953307/10000000000000 : ℝ)^4703 := by
    have hnat : (796398429 : ℕ)^5727*10000000000000^4703 ≤ 3258583953307^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796398429 2000000000 3258583953307 10000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981184803/10000000000 : ℝ)^5727 ≤ (5726454776709/25000000000000 : ℝ)^4703 := by
    have hnat : (2981184803 : ℕ)^5727*25000000000000^4703 ≤ 5726454776709^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981184803 10000000000 5726454776709 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028799733/2000000000 : ℝ)^5727 ≤ (44508341350759/100000000000000 : ℝ)^4703 := by
    have hnat : (1028799733 : ℕ)^5727*100000000000000^4703 ≤ 44508341350759^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028799733 2000000000 44508341350759 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796398429/2000000000 : ℝ), (2981184803/10000000000 : ℝ), (1028799733/2000000000 : ℝ)] ![(3258583953307/10000000000000 : ℝ), (5726454776709/25000000000000 : ℝ), (44508341350759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796398429/2000000000 : ℝ)|^5727 ≤ (3258583953307/10000000000000 : ℝ)^4703
        have hw : |(796398429/2000000000 : ℝ)|=(796398429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2981184803/10000000000 : ℝ)|^5727 ≤ (5726454776709/25000000000000 : ℝ)^4703
        have hw : |(2981184803/10000000000 : ℝ)|=(2981184803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028799733/2000000000 : ℝ)|^5727 ≤ (44508341350759/100000000000000 : ℝ)^4703
        have hw : |(1028799733/2000000000 : ℝ)|=(1028799733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s0_4 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-596553417/5000000000 : ℝ)*x 0 + (623792153/1250000000 : ℝ)*x 1 + (2811039017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (596553417/5000000000 : ℝ)^5727 ≤ (3755014557079/50000000000000 : ℝ)^4703 := by
    have hnat : (596553417 : ℕ)^5727*50000000000000^4703 ≤ 3755014557079^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596553417 5000000000 3755014557079 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623792153/1250000000 : ℝ)^5727 ≤ (5361825975459/12500000000000 : ℝ)^4703 := by
    have hnat : (623792153 : ℕ)^5727*12500000000000^4703 ≤ 5361825975459^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623792153 1250000000 5361825975459 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2811039017/5000000000 : ℝ)^5727 ≤ (2479768153179/5000000000000 : ℝ)^4703 := by
    have hnat : (2811039017 : ℕ)^5727*5000000000000^4703 ≤ 2479768153179^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2811039017 5000000000 2479768153179 5000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-596553417/5000000000 : ℝ), (623792153/1250000000 : ℝ), (2811039017/5000000000 : ℝ)] ![(3755014557079/50000000000000 : ℝ), (5361825975459/12500000000000 : ℝ), (2479768153179/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-596553417/5000000000 : ℝ)|^5727 ≤ (3755014557079/50000000000000 : ℝ)^4703
        have hw : |(-596553417/5000000000 : ℝ)|=(596553417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623792153/1250000000 : ℝ)|^5727 ≤ (5361825975459/12500000000000 : ℝ)^4703
        have hw : |(623792153/1250000000 : ℝ)|=(623792153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2811039017/5000000000 : ℝ)|^5727 ≤ (2479768153179/5000000000000 : ℝ)^4703
        have hw : |(2811039017/5000000000 : ℝ)|=(2811039017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s0_5 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598630879/5000000000 : ℝ)*x 0 + (-450463443/5000000000 : ℝ)*x 1 + (1124415629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598630879/5000000000 : ℝ)^5727 ≤ (45070174187819/100000000000000 : ℝ)^4703 := by
    have hnat : (2598630879 : ℕ)^5727*100000000000000^4703 ≤ 45070174187819^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598630879 5000000000 45070174187819 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450463443/5000000000 : ℝ)^5727 ≤ (666807693189/12500000000000 : ℝ)^4703 := by
    have hnat : (450463443 : ℕ)^5727*12500000000000^4703 ≤ 666807693189^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450463443 5000000000 666807693189 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124415629/2000000000 : ℝ)^5727 ≤ (49595364255973/100000000000000 : ℝ)^4703 := by
    have hnat : (1124415629 : ℕ)^5727*100000000000000^4703 ≤ 49595364255973^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124415629 2000000000 49595364255973 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598630879/5000000000 : ℝ), (-450463443/5000000000 : ℝ), (1124415629/2000000000 : ℝ)] ![(45070174187819/100000000000000 : ℝ), (666807693189/12500000000000 : ℝ), (49595364255973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598630879/5000000000 : ℝ)|^5727 ≤ (45070174187819/100000000000000 : ℝ)^4703
        have hw : |(2598630879/5000000000 : ℝ)|=(2598630879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450463443/5000000000 : ℝ)|^5727 ≤ (666807693189/12500000000000 : ℝ)^4703
        have hw : |(-450463443/5000000000 : ℝ)|=(450463443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124415629/2000000000 : ℝ)|^5727 ≤ (49595364255973/100000000000000 : ℝ)^4703
        have hw : |(1124415629/2000000000 : ℝ)|=(1124415629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s0_6 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103945229/200000000 : ℝ)*x 0 + (562207811/1000000000 : ℝ)*x 1 + (-225231847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103945229/200000000 : ℝ)^5727 ≤ (45070170935317/100000000000000 : ℝ)^4703 := by
    have hnat : (103945229 : ℕ)^5727*100000000000000^4703 ≤ 45070170935317^4703*200000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103945229 200000000 45070170935317 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562207811/1000000000 : ℝ)^5727 ≤ (49595363879993/100000000000000 : ℝ)^4703 := by
    have hnat : (562207811 : ℕ)^5727*100000000000000^4703 ≤ 49595363879993^4703*1000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562207811 1000000000 49595363879993 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225231847/2500000000 : ℝ)^5727 ≤ (2667232582541/50000000000000 : ℝ)^4703 := by
    have hnat : (225231847 : ℕ)^5727*50000000000000^4703 ≤ 2667232582541^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225231847 2500000000 2667232582541 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103945229/200000000 : ℝ), (562207811/1000000000 : ℝ), (-225231847/2500000000 : ℝ)] ![(45070170935317/100000000000000 : ℝ), (49595363879993/100000000000000 : ℝ), (2667232582541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103945229/200000000 : ℝ)|^5727 ≤ (45070170935317/100000000000000 : ℝ)^4703
        have hw : |(103945229/200000000 : ℝ)|=(103945229/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562207811/1000000000 : ℝ)|^5727 ≤ (49595363879993/100000000000000 : ℝ)^4703
        have hw : |(562207811/1000000000 : ℝ)|=(562207811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225231847/2500000000 : ℝ)|^5727 ≤ (2667232582541/50000000000000 : ℝ)^4703
        have hw : |(-225231847/2500000000 : ℝ)|=(225231847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s0_7 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3986630307/10000000000 : ℝ)*x 0 + (5088634961/10000000000 : ℝ)*x 1 + (759599527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3986630307/10000000000 : ℝ)^5727 ≤ (32632065040197/100000000000000 : ℝ)^4703 := by
    have hnat : (3986630307 : ℕ)^5727*100000000000000^4703 ≤ 32632065040197^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3986630307 10000000000 32632065040197 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088634961/10000000000 : ℝ)^5727 ≤ (8785138389997/20000000000000 : ℝ)^4703 := by
    have hnat : (5088634961 : ℕ)^5727*20000000000000^4703 ≤ 8785138389997^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088634961 10000000000 8785138389997 20000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759599527/2500000000 : ℝ)^5727 ≤ (23442242989349/100000000000000 : ℝ)^4703 := by
    have hnat : (759599527 : ℕ)^5727*100000000000000^4703 ≤ 23442242989349^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759599527 2500000000 23442242989349 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3986630307/10000000000 : ℝ), (5088634961/10000000000 : ℝ), (759599527/2500000000 : ℝ)] ![(32632065040197/100000000000000 : ℝ), (8785138389997/20000000000000 : ℝ), (23442242989349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3986630307/10000000000 : ℝ)|^5727 ≤ (32632065040197/100000000000000 : ℝ)^4703
        have hw : |(3986630307/10000000000 : ℝ)|=(3986630307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088634961/10000000000 : ℝ)|^5727 ≤ (8785138389997/20000000000000 : ℝ)^4703
        have hw : |(5088634961/10000000000 : ℝ)|=(5088634961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(759599527/2500000000 : ℝ)|^5727 ≤ (23442242989349/100000000000000 : ℝ)^4703
        have hw : |(759599527/2500000000 : ℝ)|=(759599527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1747_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3301/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5249/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5711/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5711 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5711*1^1024 ≤ 0^1024*1^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5711/1024 : ℝ) ≤ (60343361917299121/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5711 ≤ (60343361917299121/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5711*10000000000000000000^1024 ≤ 60343361917299121^1024*5^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 60343361917299121 10000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (60343361917299121/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5711 := by
      have hnat : (1 : ℕ)^1024*1^5711 ≤ 1^5711*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10060343361917299121/10000000000000000000 : ℝ) ≤ (2502698264464011/2500000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (10060343361917299121/10000000000000000000 : ℝ)^1024 ≤ (2502698264464011/2500000000000000 : ℝ)^5711 := by
      have hnat : (10060343361917299121 : ℕ)^1024*2500000000000000^5711 ≤ 2502698264464011^5711*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10060343361917299121 10000000000000000000 2502698264464011 2500000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502698264464011/2500000000000000 : ℝ)) (X := (10060343361917299121/10000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5060343361917299121/5000000000000000000 : ℝ) ≤ (1252698264464011/1250000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (5060343361917299121/5000000000000000000 : ℝ)^1024 ≤ (1252698264464011/1250000000000000 : ℝ)^5711 := by
      have hnat : (5060343361917299121 : ℕ)^1024*1250000000000000^5711 ≤ 1252698264464011^5711*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5060343361917299121 5000000000000000000 1252698264464011 1250000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252698264464011/1250000000000000 : ℝ)) (X := (5060343361917299121/5000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2698264464011/1000000000000000 : ℝ)*(0 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2698264464011/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60343361917299121/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2698264464011/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5711/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2698264464011/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2502698264464011/2500000000000000 : ℝ) by norm_num, show 1+(60343361917299121/10000000000000000000 : ℝ)+(0 : ℝ)=(10060343361917299121/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60343361917299121/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2698264464011/1000000000000000 : ℝ)*(2/5 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2698264464011/1000000000000000 : ℝ)*(2/5 : ℝ)=(1252698264464011/1250000000000000 : ℝ) by norm_num, show 1+2*(60343361917299121/10000000000000000000 : ℝ)=(5060343361917299121/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2698264464011/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2698264464011/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2698264464011/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2698264464011/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2698264464011/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2698264464011/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1191677787/10000000000 : ℝ)*X 0 0+(140992683/250000000 : ℝ)*X 0 1+(4973278241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687664517/5000000000 : ℝ)*X 1 0+(-1549727323/10000000000 : ℝ)*X 1 1+(198931143/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343832557/2500000000 : ℝ)*X 2 0+(994655577/2000000000 : ℝ)*X 2 1+(-1549726647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((796398429/2000000000 : ℝ)*X 0 0+(2981184803/10000000000 : ℝ)*X 0 1+(1028799733/2000000000 : ℝ)*X 0 2+(796398429/2000000000 : ℝ)*X 1 0+(2981184803/10000000000 : ℝ)*X 1 1+(1028799733/2000000000 : ℝ)*X 1 2+(796398429/2000000000 : ℝ)*X 2 0+(2981184803/10000000000 : ℝ)*X 2 1+(1028799733/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-596553417/5000000000 : ℝ)*X 0 0+(623792153/1250000000 : ℝ)*X 0 1+(2811039017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2598630879/5000000000 : ℝ)*X 1 0+(-450463443/5000000000 : ℝ)*X 1 1+(1124415629/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((103945229/200000000 : ℝ)*X 2 0+(562207811/1000000000 : ℝ)*X 2 1+(-225231847/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3986630307/10000000000 : ℝ)*X 0 0+(5088634961/10000000000 : ℝ)*X 0 1+(759599527/2500000000 : ℝ)*X 0 2+(3986630307/10000000000 : ℝ)*X 1 0+(5088634961/10000000000 : ℝ)*X 1 1+(759599527/2500000000 : ℝ)*X 1 2+(3986630307/10000000000 : ℝ)*X 2 0+(5088634961/10000000000 : ℝ)*X 2 1+(759599527/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69014137944352479351219/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187862811/20000000000000 : ℝ)*(base19) + (1206695977/100000000000000 : ℝ)*(base23) + (4914697/100000000000000 : ℝ)*(upper3) + (1417539/4000000000000 : ℝ)*(upper4) + (318109659/100000000000000 : ℝ)*(upper5) + (981455343353643/100000000000000 : ℝ)*(major0) + (981455343353643/100000000000000 : ℝ)*(major1) + (981455343353643/100000000000000 : ℝ)*(major2) + (150053808561587/10000000000000 : ℝ)*(sp0) + (750272560286509/50000000000000 : ℝ)*(sp1) + (1500544853191097/100000000000000 : ℝ)*(sp2) + (231181447257007/50000000000000 : ℝ)*(sp3) + (7974271203/100000000000000 : ℝ)*(sp4) + (1548268491/100000000000000 : ℝ)*(sp7) + (92472888556501/20000000000000 : ℝ)*(f.failure) + (750273029943537/50000000000000 : ℝ)*(f.sum) + (249089169507927/50000000000000000000000000000 : ℝ)*base66 + (622103422742073/100000000000000000000000000000 : ℝ)*base67 + (197553971757927/100000000000000000000000000000 : ℝ)*base70 + (281157518657927/100000000000000000000000000000 : ℝ)*base72 + (26172994707927/50000000000000000000000000000 : ℝ)*base74 + (478231050442073/100000000000000000000000000000 : ℝ)*base75 + (440375069057927/100000000000000000000000000000 : ℝ)*base78 + (81862674557927/100000000000000000000000000000 : ℝ)*base80 + (228806609707927/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1764097/250000000000000000000 : ℝ)*base89 + (1764097/250000000000000000000 : ℝ)*base91 + (1764097/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103960373424407993601519/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1026597209/100000000000000 : ℝ)*(base19) + (474926171/50000000000000 : ℝ)*(base23) + (3199373/12500000000000 : ℝ)*(upper2) + (179393049/100000000000000 : ℝ)*(upper3) + (78149547/50000000000000 : ℝ)*(upper5) + (517668899412257/50000000000000 : ℝ)*(major0) + (517668899412257/50000000000000 : ℝ)*(major1) + (517668899412257/50000000000000 : ℝ)*(major2) + (2216506373/50000000000000 : ℝ)*(sp1) + (1746804547/50000000000000 : ℝ)*(sp2) + (791463472941933/50000000000000 : ℝ)*(sp4) + (158292148627391/10000000000000 : ℝ)*(sp5) + (1582922502422429/100000000000000 : ℝ)*(sp6) + (121937128287831/25000000000000 : ℝ)*(sp7) + (121937128287831/25000000000000 : ℝ)*(f.failure) + (791463472941933/50000000000000 : ℝ)*(f.sum) + (86891123182827/25000000000000000000000000000 : ℝ)*base65 + (94373711382827/50000000000000000000000000000 : ℝ)*base67 + (207737693017173/50000000000000000000000000000 : ℝ)*base70 + (160028148182827/50000000000000000000000000000 : ℝ)*base71 + (82768849867173/25000000000000000000000000000 : ℝ)*base74 + (316021584182827/50000000000000000000000000000 : ℝ)*base75 + (478580431282827/50000000000000000000000000000 : ℝ)*base77 + (294464341582827/50000000000000000000000000000 : ℝ)*base79 + (125952514267173/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1508107/312500000000000000000 : ℝ)*base89 + (1508107/312500000000000000000 : ℝ)*base91 + (1508107/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1747_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3301/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5249/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1747_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1747_s1_0 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1237901037/10000000000 : ℝ)*x 0 + (5504906253/10000000000 : ℝ)*x 1 + (2538607969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1237901037/10000000000 : ℝ)^5727 ≤ (7854768385619/100000000000000 : ℝ)^4703 := by
    have hnat : (1237901037 : ℕ)^5727*100000000000000^4703 ≤ 7854768385619^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237901037 10000000000 7854768385619 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504906253/10000000000 : ℝ)^5727 ≤ (48339542705887/100000000000000 : ℝ)^4703 := by
    have hnat : (5504906253 : ℕ)^5727*100000000000000^4703 ≤ 48339542705887^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504906253 10000000000 48339542705887 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538607969/5000000000 : ℝ)^5727 ≤ (43805688897511/100000000000000 : ℝ)^4703 := by
    have hnat : (2538607969 : ℕ)^5727*100000000000000^4703 ≤ 43805688897511^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538607969 5000000000 43805688897511 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1237901037/10000000000 : ℝ), (5504906253/10000000000 : ℝ), (2538607969/5000000000 : ℝ)] ![(7854768385619/100000000000000 : ℝ), (48339542705887/100000000000000 : ℝ), (43805688897511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1237901037/10000000000 : ℝ)|^5727 ≤ (7854768385619/100000000000000 : ℝ)^4703
        have hw : |(-1237901037/10000000000 : ℝ)|=(1237901037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504906253/10000000000 : ℝ)|^5727 ≤ (48339542705887/100000000000000 : ℝ)^4703
        have hw : |(5504906253/10000000000 : ℝ)|=(5504906253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538607969/5000000000 : ℝ)|^5727 ≤ (43805688897511/100000000000000 : ℝ)^4703
        have hw : |(2538607969/5000000000 : ℝ)|=(2538607969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s1_1 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339441983/10000000000 : ℝ)*x 0 + (-1461911991/10000000000 : ℝ)*x 1 + (634651979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339441983/10000000000 : ℝ)^5727 ≤ (46576047613821/100000000000000 : ℝ)^4703 := by
    have hnat : (5339441983 : ℕ)^5727*100000000000000^4703 ≤ 46576047613821^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339441983 10000000000 46576047613821 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1461911991/10000000000 : ℝ)^5727 ≤ (2404566148199/25000000000000 : ℝ)^4703 := by
    have hnat : (1461911991 : ℕ)^5727*25000000000000^4703 ≤ 2404566148199^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461911991 10000000000 2404566148199 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634651979/1250000000 : ℝ)^5727 ≤ (1752227511353/4000000000000 : ℝ)^4703 := by
    have hnat : (634651979 : ℕ)^5727*4000000000000^4703 ≤ 1752227511353^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634651979 1250000000 1752227511353 4000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339441983/10000000000 : ℝ), (-1461911991/10000000000 : ℝ), (634651979/1250000000 : ℝ)] ![(46576047613821/100000000000000 : ℝ), (2404566148199/25000000000000 : ℝ), (1752227511353/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339441983/10000000000 : ℝ)|^5727 ≤ (46576047613821/100000000000000 : ℝ)^4703
        have hw : |(5339441983/10000000000 : ℝ)|=(5339441983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1461911991/10000000000 : ℝ)|^5727 ≤ (2404566148199/25000000000000 : ℝ)^4703
        have hw : |(-1461911991/10000000000 : ℝ)|=(1461911991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634651979/1250000000 : ℝ)|^5727 ≤ (1752227511353/4000000000000 : ℝ)^4703
        have hw : |(634651979/1250000000 : ℝ)|=(634651979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s1_2 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339441563/10000000000 : ℝ)*x 0 + (1015443221/2000000000 : ℝ)*x 1 + (-1461912189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339441563/10000000000 : ℝ)^5727 ≤ (46576043152451/100000000000000 : ℝ)^4703 := by
    have hnat : (5339441563 : ℕ)^5727*100000000000000^4703 ≤ 46576043152451^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339441563 10000000000 46576043152451 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015443221/2000000000 : ℝ)^5727 ≤ (43805690652093/100000000000000 : ℝ)^4703 := by
    have hnat : (1015443221 : ℕ)^5727*100000000000000^4703 ≤ 43805690652093^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015443221 2000000000 43805690652093 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1461912189/10000000000 : ℝ)^5727 ≤ (2404566544781/25000000000000 : ℝ)^4703 := by
    have hnat : (1461912189 : ℕ)^5727*25000000000000^4703 ≤ 2404566544781^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461912189 10000000000 2404566544781 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339441563/10000000000 : ℝ), (1015443221/2000000000 : ℝ), (-1461912189/10000000000 : ℝ)] ![(46576043152451/100000000000000 : ℝ), (43805690652093/100000000000000 : ℝ), (2404566544781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339441563/10000000000 : ℝ)|^5727 ≤ (46576043152451/100000000000000 : ℝ)^4703
        have hw : |(5339441563/10000000000 : ℝ)|=(5339441563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015443221/2000000000 : ℝ)|^5727 ≤ (43805690652093/100000000000000 : ℝ)^4703
        have hw : |(1015443221/2000000000 : ℝ)|=(1015443221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1461912189/10000000000 : ℝ)|^5727 ≤ (2404566544781/25000000000000 : ℝ)^4703
        have hw : |(-1461912189/10000000000 : ℝ)|=(1461912189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s1_3 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4026205261/10000000000 : ℝ)*x 0 + (3365190143/10000000000 : ℝ)*x 1 + (47532049/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4026205261/10000000000 : ℝ)^5727 ≤ (16513478868539/50000000000000 : ℝ)^4703 := by
    have hnat : (4026205261 : ℕ)^5727*50000000000000^4703 ≤ 16513478868539^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026205261 10000000000 16513478868539 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3365190143/10000000000 : ℝ)^5727 ≤ (26547511651959/100000000000000 : ℝ)^4703 := by
    have hnat : (3365190143 : ℕ)^5727*100000000000000^4703 ≤ 26547511651959^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3365190143 10000000000 26547511651959 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47532049/100000000 : ℝ)^5727 ≤ (40425530592249/100000000000000 : ℝ)^4703 := by
    have hnat : (47532049 : ℕ)^5727*100000000000000^4703 ≤ 40425530592249^4703*100000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47532049 100000000 40425530592249 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4026205261/10000000000 : ℝ), (3365190143/10000000000 : ℝ), (47532049/100000000 : ℝ)] ![(16513478868539/50000000000000 : ℝ), (26547511651959/100000000000000 : ℝ), (40425530592249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4026205261/10000000000 : ℝ)|^5727 ≤ (16513478868539/50000000000000 : ℝ)^4703
        have hw : |(4026205261/10000000000 : ℝ)|=(4026205261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3365190143/10000000000 : ℝ)|^5727 ≤ (26547511651959/100000000000000 : ℝ)^4703
        have hw : |(3365190143/10000000000 : ℝ)|=(3365190143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47532049/100000000 : ℝ)|^5727 ≤ (40425530592249/100000000000000 : ℝ)^4703
        have hw : |(47532049/100000000 : ℝ)|=(47532049/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s1_4 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-619137971/5000000000 : ℝ)*x 0 + (5084250411/10000000000 : ℝ)*x 1 + (5497721593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (619137971/5000000000 : ℝ)^5727 ≤ (7857665297009/100000000000000 : ℝ)^4703 := by
    have hnat : (619137971 : ℕ)^5727*100000000000000^4703 ≤ 7857665297009^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619137971 5000000000 7857665297009 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084250411/10000000000 : ℝ)^5727 ≤ (43879607564987/100000000000000 : ℝ)^4703 := by
    have hnat : (5084250411 : ℕ)^5727*100000000000000^4703 ≤ 43879607564987^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084250411 10000000000 43879607564987 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497721593/10000000000 : ℝ)^5727 ≤ (48262727127877/100000000000000 : ℝ)^4703 := by
    have hnat : (5497721593 : ℕ)^5727*100000000000000^4703 ≤ 48262727127877^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497721593 10000000000 48262727127877 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-619137971/5000000000 : ℝ), (5084250411/10000000000 : ℝ), (5497721593/10000000000 : ℝ)] ![(7857665297009/100000000000000 : ℝ), (43879607564987/100000000000000 : ℝ), (48262727127877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-619137971/5000000000 : ℝ)|^5727 ≤ (7857665297009/100000000000000 : ℝ)^4703
        have hw : |(-619137971/5000000000 : ℝ)|=(619137971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084250411/10000000000 : ℝ)|^5727 ≤ (43879607564987/100000000000000 : ℝ)^4703
        have hw : |(5084250411/10000000000 : ℝ)|=(5084250411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497721593/10000000000 : ℝ)|^5727 ≤ (48262727127877/100000000000000 : ℝ)^4703
        have hw : |(5497721593/10000000000 : ℝ)|=(5497721593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s1_5 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225956183/10000000000 : ℝ)*x 0 + (-520703099/5000000000 : ℝ)*x 1 + (5497721819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225956183/10000000000 : ℝ)^5727 ≤ (5671671403811/12500000000000 : ℝ)^4703 := by
    have hnat : (5225956183 : ℕ)^5727*12500000000000^4703 ≤ 5671671403811^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225956183 10000000000 5671671403811 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520703099/5000000000 : ℝ)^5727 ≤ (6363899208211/100000000000000 : ℝ)^4703 := by
    have hnat : (520703099 : ℕ)^5727*100000000000000^4703 ≤ 6363899208211^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520703099 5000000000 6363899208211 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497721819/10000000000 : ℝ)^5727 ≤ (48262729543837/100000000000000 : ℝ)^4703 := by
    have hnat : (5497721819 : ℕ)^5727*100000000000000^4703 ≤ 48262729543837^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497721819 10000000000 48262729543837 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225956183/10000000000 : ℝ), (-520703099/5000000000 : ℝ), (5497721819/10000000000 : ℝ)] ![(5671671403811/12500000000000 : ℝ), (6363899208211/100000000000000 : ℝ), (48262729543837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225956183/10000000000 : ℝ)|^5727 ≤ (5671671403811/12500000000000 : ℝ)^4703
        have hw : |(5225956183/10000000000 : ℝ)|=(5225956183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520703099/5000000000 : ℝ)|^5727 ≤ (6363899208211/100000000000000 : ℝ)^4703
        have hw : |(-520703099/5000000000 : ℝ)|=(520703099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497721819/10000000000 : ℝ)|^5727 ≤ (48262729543837/100000000000000 : ℝ)^4703
        have hw : |(5497721819/10000000000 : ℝ)|=(5497721819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s1_6 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045191203/2000000000 : ℝ)*x 0 + (5497721969/10000000000 : ℝ)*x 1 + (-1041406221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045191203/2000000000 : ℝ)^5727 ≤ (11343342363567/25000000000000 : ℝ)^4703 := by
    have hnat : (1045191203 : ℕ)^5727*25000000000000^4703 ≤ 11343342363567^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045191203 2000000000 11343342363567 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497721969/10000000000 : ℝ)^5727 ≤ (48262731147351/100000000000000 : ℝ)^4703 := by
    have hnat : (5497721969 : ℕ)^5727*100000000000000^4703 ≤ 48262731147351^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497721969 10000000000 48262731147351 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041406221/10000000000 : ℝ)^5727 ≤ (6363899379363/100000000000000 : ℝ)^4703 := by
    have hnat : (1041406221 : ℕ)^5727*100000000000000^4703 ≤ 6363899379363^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041406221 10000000000 6363899379363 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045191203/2000000000 : ℝ), (5497721969/10000000000 : ℝ), (-1041406221/10000000000 : ℝ)] ![(11343342363567/25000000000000 : ℝ), (48262731147351/100000000000000 : ℝ), (6363899379363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045191203/2000000000 : ℝ)|^5727 ≤ (11343342363567/25000000000000 : ℝ)^4703
        have hw : |(1045191203/2000000000 : ℝ)|=(1045191203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497721969/10000000000 : ℝ)|^5727 ≤ (48262731147351/100000000000000 : ℝ)^4703
        have hw : |(5497721969/10000000000 : ℝ)|=(5497721969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041406221/10000000000 : ℝ)|^5727 ≤ (6363899379363/100000000000000 : ℝ)^4703
        have hw : |(-1041406221/10000000000 : ℝ)|=(1041406221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s1_7 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4027421953/10000000000 : ℝ)*x 0 + (2365188253/5000000000 : ℝ)*x 1 + (3388505583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4027421953/10000000000 : ℝ)^5727 ≤ (8259777938257/25000000000000 : ℝ)^4703 := by
    have hnat : (4027421953 : ℕ)^5727*25000000000000^4703 ≤ 8259777938257^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027421953 10000000000 8259777938257 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2365188253/5000000000 : ℝ)^5727 ≤ (803784550731/2000000000000 : ℝ)^4703 := by
    have hnat : (2365188253 : ℕ)^5727*2000000000000^4703 ≤ 803784550731^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365188253 5000000000 803784550731 2000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3388505583/10000000000 : ℝ)^5727 ≤ (2677166069853/10000000000000 : ℝ)^4703 := by
    have hnat : (3388505583 : ℕ)^5727*10000000000000^4703 ≤ 2677166069853^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3388505583 10000000000 2677166069853 10000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4027421953/10000000000 : ℝ), (2365188253/5000000000 : ℝ), (3388505583/10000000000 : ℝ)] ![(8259777938257/25000000000000 : ℝ), (803784550731/2000000000000 : ℝ), (2677166069853/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4027421953/10000000000 : ℝ)|^5727 ≤ (8259777938257/25000000000000 : ℝ)^4703
        have hw : |(4027421953/10000000000 : ℝ)|=(4027421953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2365188253/5000000000 : ℝ)|^5727 ≤ (803784550731/2000000000000 : ℝ)^4703
        have hw : |(2365188253/5000000000 : ℝ)|=(2365188253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3388505583/10000000000 : ℝ)|^5727 ≤ (2677166069853/10000000000000 : ℝ)^4703
        have hw : |(3388505583/10000000000 : ℝ)|=(3388505583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1747_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5249/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4467/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3623/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5249/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3301/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5249/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3301/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5249/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3301/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5249/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3301/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5249/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3301/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5249/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3301/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3301/50000 : ℝ) ^ (5711/1024 : ℝ) ≤ (13065474147053/50000000000000000000 : ℝ) := by
    have hpowers : (3301/50000 : ℝ)^5711 ≤ (13065474147053/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3301 : ℕ)^5711*50000000000000000000^1024 ≤ 13065474147053^1024*50000^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3301 50000 13065474147053 50000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3301/50000 : ℝ)) (X := (13065474147053/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5249/25000 : ℝ) ^ (5711/1024 : ℝ) ≤ (16575055741858651/100000000000000000000 : ℝ) := by
    have hpowers : (5249/25000 : ℝ)^5711 ≤ (16575055741858651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5249 : ℕ)^5711*100000000000000000000^1024 ≤ 16575055741858651^1024*25000^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5249 25000 16575055741858651 100000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5249/25000 : ℝ)) (X := (16575055741858651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013065474147053/25000000000000000000 : ℝ) ≤ (10000000937071803/10000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (25000013065474147053/25000000000000000000 : ℝ)^1024 ≤ (10000000937071803/10000000000000000 : ℝ)^5711 := by
      have hnat : (25000013065474147053 : ℕ)^1024*10000000000000000^5711 ≤ 10000000937071803^5711*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013065474147053 25000000000000000000 10000000937071803 10000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000937071803/10000000000000000 : ℝ)) (X := (25000013065474147053/25000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016601186690152757/100000000000000000000 : ℝ) ≤ (5000148822073433/5000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (100016601186690152757/100000000000000000000 : ℝ)^1024 ≤ (5000148822073433/5000000000000000 : ℝ)^5711 := by
      have hnat : (100016601186690152757 : ℕ)^1024*5000000000000000^5711 ≤ 5000148822073433^5711*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016601186690152757 100000000000000000000 5000148822073433 5000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000148822073433/5000000000000000 : ℝ)) (X := (100016601186690152757/100000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016575055741858651/50000000000000000000 : ℝ) ≤ (10000594351221929/10000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (50016575055741858651/50000000000000000000 : ℝ)^1024 ≤ (10000594351221929/10000000000000000 : ℝ)^5711 := by
      have hnat : (50016575055741858651 : ℕ)^1024*10000000000000000^5711 ≤ 10000594351221929^5711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016575055741858651 50000000000000000000 10000594351221929 10000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000594351221929/10000000000000000 : ℝ)) (X := (50016575055741858651/50000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13065474147053/50000000000000000000 : ℝ) ≤ ((14393609576799240053/14394000000000000000 : ℝ)+2*(296707075063/1439400000000000 : ℝ)*(3301/50000 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (14393609576799240053/14394000000000000000 : ℝ)+2*(296707075063/1439400000000000 : ℝ)*(3301/50000 : ℝ)=(10000000937071803/10000000000000000 : ℝ) by norm_num, show 1+2*(13065474147053/50000000000000000000 : ℝ)=(25000013065474147053/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16575055741858651/100000000000000000000 : ℝ)+(13065474147053/50000000000000000000 : ℝ) ≤ ((14393609576799240053/14394000000000000000 : ℝ)+(296707075063/1439400000000000 : ℝ)*((5249/25000 : ℝ)+(3301/50000 : ℝ)))^(5711/1024 : ℝ) := by
    rw [show (14393609576799240053/14394000000000000000 : ℝ)+(296707075063/1439400000000000 : ℝ)*((5249/25000 : ℝ)+(3301/50000 : ℝ))=(5000148822073433/5000000000000000 : ℝ) by norm_num, show 1+(16575055741858651/100000000000000000000 : ℝ)+(13065474147053/50000000000000000000 : ℝ)=(100016601186690152757/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16575055741858651/100000000000000000000 : ℝ) ≤ ((14393609576799240053/14394000000000000000 : ℝ)+2*(296707075063/1439400000000000 : ℝ)*(5249/25000 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (14393609576799240053/14394000000000000000 : ℝ)+2*(296707075063/1439400000000000 : ℝ)*(5249/25000 : ℝ)=(10000594351221929/10000000000000000 : ℝ) by norm_num, show 1+2*(16575055741858651/100000000000000000000 : ℝ)=(50016575055741858651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14393609576799240053/14394000000000000000 : ℝ)*(X 1 0+X 2 0)+(296707075063/1439400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (3301/50000 : ℝ)) (hi := (5249/25000 : ℝ)) (c := (14393609576799240053/14394000000000000000 : ℝ)) (alpha := (296707075063/1439400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14393609576799240053/14394000000000000000 : ℝ)*(X 0 1+X 2 1)+(296707075063/1439400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (3301/50000 : ℝ)) (hi := (5249/25000 : ℝ)) (c := (14393609576799240053/14394000000000000000 : ℝ)) (alpha := (296707075063/1439400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14393609576799240053/14394000000000000000 : ℝ)*(X 0 2+X 1 2)+(296707075063/1439400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (3301/50000 : ℝ)) (hi := (5249/25000 : ℝ)) (c := (14393609576799240053/14394000000000000000 : ℝ)) (alpha := (296707075063/1439400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1237901037/10000000000 : ℝ)*X 0 0+(5504906253/10000000000 : ℝ)*X 0 1+(2538607969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5339441983/10000000000 : ℝ)*X 1 0+(-1461911991/10000000000 : ℝ)*X 1 1+(634651979/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5339441563/10000000000 : ℝ)*X 2 0+(1015443221/2000000000 : ℝ)*X 2 1+(-1461912189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4026205261/10000000000 : ℝ)*X 0 0+(3365190143/10000000000 : ℝ)*X 0 1+(47532049/100000000 : ℝ)*X 0 2+(4026205261/10000000000 : ℝ)*X 1 0+(3365190143/10000000000 : ℝ)*X 1 1+(47532049/100000000 : ℝ)*X 1 2+(4026205261/10000000000 : ℝ)*X 2 0+(3365190143/10000000000 : ℝ)*X 2 1+(47532049/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-619137971/5000000000 : ℝ)*X 0 0+(5084250411/10000000000 : ℝ)*X 0 1+(5497721593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5225956183/10000000000 : ℝ)*X 1 0+(-520703099/5000000000 : ℝ)*X 1 1+(5497721819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1045191203/2000000000 : ℝ)*X 2 0+(5497721969/10000000000 : ℝ)*X 2 1+(-1041406221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4027421953/10000000000 : ℝ)*X 0 0+(2365188253/5000000000 : ℝ)*X 0 1+(3388505583/10000000000 : ℝ)*X 0 2+(4027421953/10000000000 : ℝ)*X 1 0+(2365188253/5000000000 : ℝ)*X 1 1+(3388505583/10000000000 : ℝ)*X 1 2+(4027421953/10000000000 : ℝ)*X 2 0+(2365188253/5000000000 : ℝ)*X 2 1+(3388505583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (412211564167031800850887041/29987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127279081/6250000000000 : ℝ)*(base19) + (210808139/12500000000000 : ℝ)*(base23) + (88677473/100000000000000 : ℝ)*(lower2) + (403738121/100000000000000 : ℝ)*(upper3) + (75246529/50000000000000 : ℝ)*(upper5) + (382329186612603/25000000000000 : ℝ)*(major0) + (382329186612603/25000000000000 : ℝ)*(major1) + (382329186612603/25000000000000 : ℝ)*(major2) + (116907848571167/5000000000000 : ℝ)*(sp0) + (2338168584838267/100000000000000 : ℝ)*(sp1) + (584542233709613/25000000000000 : ℝ)*(sp2) + (72045727783861/10000000000000 : ℝ)*(sp3) + (13649880223/100000000000000 : ℝ)*(sp4) + (41084439/800000000000 : ℝ)*(sp7) + (360231206696743/50000000000000 : ℝ)*(f.failure) + (2338170621303563/100000000000000 : ℝ)*(f.sum) + (59964626608521/11995000000000000000000000000 : ℝ)*base65 + (172776107673342653/119950000000000000000000000000000 : ℝ)*base67 + (1157511674434892653/119950000000000000000000000000000 : ℝ)*base69 + (567578710857992653/119950000000000000000000000000000 : ℝ)*base71 + (12703979425241/11995000000000000000000000000 : ℝ)*base73 + (1382070670984142653/119950000000000000000000000000000 : ℝ)*base75 + (661785399908742653/119950000000000000000000000000000 : ℝ)*base77 + (247409076627307347/119950000000000000000000000000000 : ℝ)*base80 + (95358689838811/11995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4974571/625000000000000000000 : ℝ)*base89 + (4974571/625000000000000000000 : ℝ)*base91 + (4974571/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (792960844415394334909498661/59975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (873507787/50000000000000 : ℝ)*(base19) + (188362417/10000000000000 : ℝ)*(base23) + (169287811/50000000000000 : ℝ)*(upper3) + (86355079/100000000000000 : ℝ)*(lower4) + (56331521/25000000000000 : ℝ)*(upper5) + (790943559693937/50000000000000 : ℝ)*(major0) + (790943559693937/50000000000000 : ℝ)*(major1) + (790943559693937/50000000000000 : ℝ)*(major2) + (5976591657/50000000000000 : ℝ)*(sp1) + (14214952179/100000000000000 : ℝ)*(sp2) + (604636359371951/25000000000000 : ℝ)*(sp4) + (483706347457783/20000000000000 : ℝ)*(sp5) + (1209264669455727/50000000000000 : ℝ)*(sp6) + (93153545071313/12500000000000 : ℝ)*(sp7) + (93153545071313/12500000000000 : ℝ)*(f.failure) + (604636359371951/25000000000000 : ℝ)*(f.sum) + (103177332953191/35985000000000000000000000000 : ℝ)*base65 + (505370421405877113/239900000000000000000000000000000 : ℝ)*base68 + (1359896413132277113/239900000000000000000000000000000 : ℝ)*base70 + (343709819449222887/239900000000000000000000000000000 : ℝ)*base71 + (1916958001769/35985000000000000000000000000 : ℝ)*base74 + (596153618586177113/239900000000000000000000000000000 : ℝ)*base76 + (358100472902777113/239900000000000000000000000000000 : ℝ)*base78 + (488742539058177113/239900000000000000000000000000000 : ℝ)*base80 + (932587409741/8996250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2277861/156250000000000000000 : ℝ)*base89 + (2277861/156250000000000000000 : ℝ)*base91 + (2277861/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1747_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5249/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3301/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4467/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3623/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1747_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1747_s2_0 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1239069071/10000000000 : ℝ)*x 0 + (1375290767/2500000000 : ℝ)*x 1 + (1016033211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1239069071/10000000000 : ℝ)^5727 ≤ (7863794477379/100000000000000 : ℝ)^4703 := by
    have hnat : (1239069071 : ℕ)^5727*100000000000000^4703 ≤ 7863794477379^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239069071 10000000000 7863794477379 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375290767/2500000000 : ℝ)^5727 ≤ (48299519308563/100000000000000 : ℝ)^4703 := by
    have hnat : (1375290767 : ℕ)^5727*100000000000000^4703 ≤ 48299519308563^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375290767 2500000000 48299519308563 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016033211/2000000000 : ℝ)^5727 ≤ (43836686192159/100000000000000 : ℝ)^4703 := by
    have hnat : (1016033211 : ℕ)^5727*100000000000000^4703 ≤ 43836686192159^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016033211 2000000000 43836686192159 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1239069071/10000000000 : ℝ), (1375290767/2500000000 : ℝ), (1016033211/2000000000 : ℝ)] ![(7863794477379/100000000000000 : ℝ), (48299519308563/100000000000000 : ℝ), (43836686192159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1239069071/10000000000 : ℝ)|^5727 ≤ (7863794477379/100000000000000 : ℝ)^4703
        have hw : |(-1239069071/10000000000 : ℝ)|=(1239069071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375290767/2500000000 : ℝ)|^5727 ≤ (48299519308563/100000000000000 : ℝ)^4703
        have hw : |(1375290767/2500000000 : ℝ)|=(1375290767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016033211/2000000000 : ℝ)|^5727 ≤ (43836686192159/100000000000000 : ℝ)^4703
        have hw : |(1016033211/2000000000 : ℝ)|=(1016033211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s2_1 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067681113/2000000000 : ℝ)*x 0 + (-729708281/5000000000 : ℝ)*x 1 + (5080166013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067681113/2000000000 : ℝ)^5727 ≤ (46565038693371/100000000000000 : ℝ)^4703 := by
    have hnat : (1067681113 : ℕ)^5727*100000000000000^4703 ≤ 46565038693371^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067681113 2000000000 46565038693371 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729708281/5000000000 : ℝ)^5727 ≤ (4799137771153/50000000000000 : ℝ)^4703 := by
    have hnat : (729708281 : ℕ)^5727*50000000000000^4703 ≤ 4799137771153^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729708281 5000000000 4799137771153 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080166013/10000000000 : ℝ)^5727 ≤ (43836685750831/100000000000000 : ℝ)^4703 := by
    have hnat : (5080166013 : ℕ)^5727*100000000000000^4703 ≤ 43836685750831^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080166013 10000000000 43836685750831 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067681113/2000000000 : ℝ), (-729708281/5000000000 : ℝ), (5080166013/10000000000 : ℝ)] ![(46565038693371/100000000000000 : ℝ), (4799137771153/50000000000000 : ℝ), (43836685750831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067681113/2000000000 : ℝ)|^5727 ≤ (46565038693371/100000000000000 : ℝ)^4703
        have hw : |(1067681113/2000000000 : ℝ)|=(1067681113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-729708281/5000000000 : ℝ)|^5727 ≤ (4799137771153/50000000000000 : ℝ)^4703
        have hw : |(-729708281/5000000000 : ℝ)|=(729708281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080166013/10000000000 : ℝ)|^5727 ≤ (43836685750831/100000000000000 : ℝ)^4703
        have hw : |(5080166013/10000000000 : ℝ)|=(5080166013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s2_2 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5338405661/10000000000 : ℝ)*x 0 + (2540083049/5000000000 : ℝ)*x 1 + (-1459416323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5338405661/10000000000 : ℝ)^5727 ≤ (4656503971307/10000000000000 : ℝ)^4703 := by
    have hnat : (5338405661 : ℕ)^5727*10000000000000^4703 ≤ 4656503971307^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338405661 10000000000 4656503971307 10000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540083049/5000000000 : ℝ)^5727 ≤ (21918343321997/50000000000000 : ℝ)^4703 := by
    have hnat : (2540083049 : ℕ)^5727*50000000000000^4703 ≤ 21918343321997^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540083049 5000000000 21918343321997 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1459416323/10000000000 : ℝ)^5727 ≤ (599892101763/6250000000000 : ℝ)^4703 := by
    have hnat : (1459416323 : ℕ)^5727*6250000000000^4703 ≤ 599892101763^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459416323 10000000000 599892101763 6250000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5338405661/10000000000 : ℝ), (2540083049/5000000000 : ℝ), (-1459416323/10000000000 : ℝ)] ![(4656503971307/10000000000000 : ℝ), (21918343321997/50000000000000 : ℝ), (599892101763/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5338405661/10000000000 : ℝ)|^5727 ≤ (4656503971307/10000000000000 : ℝ)^4703
        have hw : |(5338405661/10000000000 : ℝ)|=(5338405661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540083049/5000000000 : ℝ)|^5727 ≤ (21918343321997/50000000000000 : ℝ)^4703
        have hw : |(2540083049/5000000000 : ℝ)|=(2540083049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1459416323/10000000000 : ℝ)|^5727 ≤ (599892101763/6250000000000 : ℝ)^4703
        have hw : |(-1459416323/10000000000 : ℝ)|=(1459416323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s2_3 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4027160163/10000000000 : ℝ)*x 0 + (3375978187/10000000000 : ℝ)*x 1 + (2371135507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4027160163/10000000000 : ℝ)^5727 ≤ (16518248281011/50000000000000 : ℝ)^4703 := by
    have hnat : (4027160163 : ℕ)^5727*50000000000000^4703 ≤ 16518248281011^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027160163 10000000000 16518248281011 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3375978187/10000000000 : ℝ)^5727 ≤ (26651183428839/100000000000000 : ℝ)^4703 := by
    have hnat : (3375978187 : ℕ)^5727*100000000000000^4703 ≤ 26651183428839^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3375978187 10000000000 26651183428839 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2371135507/5000000000 : ℝ)^5727 ≤ (20156159995089/50000000000000 : ℝ)^4703 := by
    have hnat : (2371135507 : ℕ)^5727*50000000000000^4703 ≤ 20156159995089^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371135507 5000000000 20156159995089 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4027160163/10000000000 : ℝ), (3375978187/10000000000 : ℝ), (2371135507/5000000000 : ℝ)] ![(16518248281011/50000000000000 : ℝ), (26651183428839/100000000000000 : ℝ), (20156159995089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4027160163/10000000000 : ℝ)|^5727 ≤ (16518248281011/50000000000000 : ℝ)^4703
        have hw : |(4027160163/10000000000 : ℝ)|=(4027160163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3375978187/10000000000 : ℝ)|^5727 ≤ (26651183428839/100000000000000 : ℝ)^4703
        have hw : |(3375978187/10000000000 : ℝ)|=(3375978187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2371135507/5000000000 : ℝ)|^5727 ≤ (20156159995089/50000000000000 : ℝ)^4703
        have hw : |(2371135507/5000000000 : ℝ)|=(2371135507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s2_4 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1239426351/10000000000 : ℝ)*x 0 + (635872757/1250000000 : ℝ)*x 1 + (5494203999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1239426351/10000000000 : ℝ)^5727 ≤ (7866555762037/100000000000000 : ℝ)^4703 := by
    have hnat : (1239426351 : ℕ)^5727*100000000000000^4703 ≤ 7866555762037^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239426351 10000000000 7866555762037 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635872757/1250000000 : ℝ)^5727 ≤ (21954158930277/50000000000000 : ℝ)^4703 := by
    have hnat : (635872757 : ℕ)^5727*50000000000000^4703 ≤ 21954158930277^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635872757 1250000000 21954158930277 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494203999/10000000000 : ℝ)^5727 ≤ (120562815887/250000000000 : ℝ)^4703 := by
    have hnat : (5494203999 : ℕ)^5727*250000000000^4703 ≤ 120562815887^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494203999 10000000000 120562815887 250000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1239426351/10000000000 : ℝ), (635872757/1250000000 : ℝ), (5494203999/10000000000 : ℝ)] ![(7866555762037/100000000000000 : ℝ), (21954158930277/50000000000000 : ℝ), (120562815887/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1239426351/10000000000 : ℝ)|^5727 ≤ (7866555762037/100000000000000 : ℝ)^4703
        have hw : |(-1239426351/10000000000 : ℝ)|=(1239426351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635872757/1250000000 : ℝ)|^5727 ≤ (21954158930277/50000000000000 : ℝ)^4703
        have hw : |(635872757/1250000000 : ℝ)|=(635872757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494203999/10000000000 : ℝ)|^5727 ≤ (120562815887/250000000000 : ℝ)^4703
        have hw : |(5494203999/10000000000 : ℝ)|=(5494203999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s2_5 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226715673/10000000000 : ℝ)*x 0 + (-522689341/5000000000 : ℝ)*x 1 + (5494204001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226715673/10000000000 : ℝ)^5727 ≤ (709084394479/1562500000000 : ℝ)^4703 := by
    have hnat : (5226715673 : ℕ)^5727*1562500000000^4703 ≤ 709084394479^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226715673 10000000000 709084394479 1562500000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522689341/5000000000 : ℝ)^5727 ≤ (799184045161/12500000000000 : ℝ)^4703 := by
    have hnat : (522689341 : ℕ)^5727*12500000000000^4703 ≤ 799184045161^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522689341 5000000000 799184045161 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494204001/10000000000 : ℝ)^5727 ≤ (48225126376177/100000000000000 : ℝ)^4703 := by
    have hnat : (5494204001 : ℕ)^5727*100000000000000^4703 ≤ 48225126376177^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494204001 10000000000 48225126376177 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226715673/10000000000 : ℝ), (-522689341/5000000000 : ℝ), (5494204001/10000000000 : ℝ)] ![(709084394479/1562500000000 : ℝ), (799184045161/12500000000000 : ℝ), (48225126376177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226715673/10000000000 : ℝ)|^5727 ≤ (709084394479/1562500000000 : ℝ)^4703
        have hw : |(5226715673/10000000000 : ℝ)|=(5226715673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522689341/5000000000 : ℝ)|^5727 ≤ (799184045161/12500000000000 : ℝ)^4703
        have hw : |(-522689341/5000000000 : ℝ)|=(522689341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494204001/10000000000 : ℝ)|^5727 ≤ (48225126376177/100000000000000 : ℝ)^4703
        have hw : |(5494204001/10000000000 : ℝ)|=(5494204001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s2_6 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613357837/5000000000 : ℝ)*x 0 + (1373551/2500000 : ℝ)*x 1 + (-522689341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613357837/5000000000 : ℝ)^5727 ≤ (45381401257229/100000000000000 : ℝ)^4703 := by
    have hnat : (2613357837 : ℕ)^5727*100000000000000^4703 ≤ 45381401257229^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613357837 5000000000 45381401257229 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373551/2500000 : ℝ)^5727 ≤ (48225126365489/100000000000000 : ℝ)^4703 := by
    have hnat : (1373551 : ℕ)^5727*100000000000000^4703 ≤ 48225126365489^4703*2500000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373551 2500000 48225126365489 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522689341/5000000000 : ℝ)^5727 ≤ (799184045161/12500000000000 : ℝ)^4703 := by
    have hnat : (522689341 : ℕ)^5727*12500000000000^4703 ≤ 799184045161^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522689341 5000000000 799184045161 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613357837/5000000000 : ℝ), (1373551/2500000 : ℝ), (-522689341/5000000000 : ℝ)] ![(45381401257229/100000000000000 : ℝ), (48225126365489/100000000000000 : ℝ), (799184045161/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613357837/5000000000 : ℝ)|^5727 ≤ (45381401257229/100000000000000 : ℝ)^4703
        have hw : |(2613357837/5000000000 : ℝ)|=(2613357837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373551/2500000 : ℝ)|^5727 ≤ (48225126365489/100000000000000 : ℝ)^4703
        have hw : |(1373551/2500000 : ℝ)|=(1373551/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522689341/5000000000 : ℝ)|^5727 ≤ (799184045161/12500000000000 : ℝ)^4703
        have hw : |(-522689341/5000000000 : ℝ)|=(522689341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s2_7 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4028320387/10000000000 : ℝ)*x 0 + (590018869/1250000000 : ℝ)*x 1 + (3398562829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4028320387/10000000000 : ℝ)^5727 ≤ (16524043538767/50000000000000 : ℝ)^4703 := by
    have hnat : (4028320387 : ℕ)^5727*50000000000000^4703 ≤ 16524043538767^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028320387 10000000000 16524043538767 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590018869/1250000000 : ℝ)^5727 ≤ (10020865101241/25000000000000 : ℝ)^4703 := by
    have hnat : (590018869 : ℕ)^5727*25000000000000^4703 ≤ 10020865101241^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590018869 1250000000 10020865101241 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3398562829/10000000000 : ℝ)^5727 ≤ (13434226251107/50000000000000 : ℝ)^4703 := by
    have hnat : (3398562829 : ℕ)^5727*50000000000000^4703 ≤ 13434226251107^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3398562829 10000000000 13434226251107 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4028320387/10000000000 : ℝ), (590018869/1250000000 : ℝ), (3398562829/10000000000 : ℝ)] ![(16524043538767/50000000000000 : ℝ), (10020865101241/25000000000000 : ℝ), (13434226251107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4028320387/10000000000 : ℝ)|^5727 ≤ (16524043538767/50000000000000 : ℝ)^4703
        have hw : |(4028320387/10000000000 : ℝ)|=(4028320387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(590018869/1250000000 : ℝ)|^5727 ≤ (10020865101241/25000000000000 : ℝ)^4703
        have hw : |(590018869/1250000000 : ℝ)|=(590018869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3398562829/10000000000 : ℝ)|^5727 ≤ (13434226251107/50000000000000 : ℝ)^4703
        have hw : |(3398562829/10000000000 : ℝ)|=(3398562829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1747_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3623/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9/100 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3607/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3623/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4467/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3623/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4467/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3623/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4467/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3623/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4467/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3623/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4467/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3623/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4467/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4467/50000 : ℝ) ^ (5711/1024 : ℝ) ≤ (70598837999853/50000000000000000000 : ℝ) := by
    have hpowers : (4467/50000 : ℝ)^5711 ≤ (70598837999853/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4467 : ℕ)^5711*50000000000000000000^1024 ≤ 70598837999853^1024*50000^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4467 50000 70598837999853 50000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4467/50000 : ℝ)) (X := (70598837999853/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3623/20000 : ℝ) ^ (5711/1024 : ℝ) ≤ (1455457987457463/20000000000000000000 : ℝ) := by
    have hpowers : (3623/20000 : ℝ)^5711 ≤ (1455457987457463/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3623 : ℕ)^5711*20000000000000000000^1024 ≤ 1455457987457463^1024*20000^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3623 20000 1455457987457463 20000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3623/20000 : ℝ)) (X := (1455457987457463/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000070598837999853/25000000000000000000 : ℝ) ≤ (10000005063430317/10000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (25000070598837999853/25000000000000000000 : ℝ)^1024 ≤ (10000005063430317/10000000000000000 : ℝ)^5711 := by
      have hnat : (25000070598837999853 : ℕ)^1024*10000000000000000^5711 ≤ 10000005063430317^5711*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000070598837999853 25000000000000000000 10000005063430317 10000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005063430317/10000000000000000 : ℝ)) (X := (25000070598837999853/25000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100007418487613287021/100000000000000000000 : ℝ) ≤ (2500033252933267/2500000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (100007418487613287021/100000000000000000000 : ℝ)^1024 ≤ (2500033252933267/2500000000000000 : ℝ)^5711 := by
      have hnat : (100007418487613287021 : ℕ)^1024*2500000000000000^5711 ≤ 2500033252933267^5711*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100007418487613287021 100000000000000000000 2500033252933267 2500000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500033252933267/2500000000000000 : ℝ)) (X := (100007418487613287021/100000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001455457987457463/10000000000000000000 : ℝ) ≤ (10000260960035819/10000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (10001455457987457463/10000000000000000000 : ℝ)^1024 ≤ (10000260960035819/10000000000000000 : ℝ)^5711 := by
      have hnat : (10001455457987457463 : ℕ)^1024*10000000000000000^5711 ≤ 10000260960035819^5711*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001455457987457463 10000000000000000000 10000260960035819 10000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000260960035819/10000000000000000 : ℝ)) (X := (10001455457987457463/10000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(70598837999853/50000000000000000000 : ℝ) ≤ ((91807760307080185509/91810000000000000000 : ℝ)+2*(127948302751/918100000000000 : ℝ)*(4467/50000 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (91807760307080185509/91810000000000000000 : ℝ)+2*(127948302751/918100000000000 : ℝ)*(4467/50000 : ℝ)=(10000005063430317/10000000000000000 : ℝ) by norm_num, show 1+2*(70598837999853/50000000000000000000 : ℝ)=(25000070598837999853/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1455457987457463/20000000000000000000 : ℝ)+(70598837999853/50000000000000000000 : ℝ) ≤ ((91807760307080185509/91810000000000000000 : ℝ)+(127948302751/918100000000000 : ℝ)*((3623/20000 : ℝ)+(4467/50000 : ℝ)))^(5711/1024 : ℝ) := by
    rw [show (91807760307080185509/91810000000000000000 : ℝ)+(127948302751/918100000000000 : ℝ)*((3623/20000 : ℝ)+(4467/50000 : ℝ))=(2500033252933267/2500000000000000 : ℝ) by norm_num, show 1+(1455457987457463/20000000000000000000 : ℝ)+(70598837999853/50000000000000000000 : ℝ)=(100007418487613287021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1455457987457463/20000000000000000000 : ℝ) ≤ ((91807760307080185509/91810000000000000000 : ℝ)+2*(127948302751/918100000000000 : ℝ)*(3623/20000 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (91807760307080185509/91810000000000000000 : ℝ)+2*(127948302751/918100000000000 : ℝ)*(3623/20000 : ℝ)=(10000260960035819/10000000000000000 : ℝ) by norm_num, show 1+2*(1455457987457463/20000000000000000000 : ℝ)=(10001455457987457463/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (91807760307080185509/91810000000000000000 : ℝ)*(X 1 0+X 2 0)+(127948302751/918100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (4467/50000 : ℝ)) (hi := (3623/20000 : ℝ)) (c := (91807760307080185509/91810000000000000000 : ℝ)) (alpha := (127948302751/918100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (91807760307080185509/91810000000000000000 : ℝ)*(X 0 1+X 2 1)+(127948302751/918100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (4467/50000 : ℝ)) (hi := (3623/20000 : ℝ)) (c := (91807760307080185509/91810000000000000000 : ℝ)) (alpha := (127948302751/918100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (91807760307080185509/91810000000000000000 : ℝ)*(X 0 2+X 1 2)+(127948302751/918100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (4467/50000 : ℝ)) (hi := (3623/20000 : ℝ)) (c := (91807760307080185509/91810000000000000000 : ℝ)) (alpha := (127948302751/918100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1239069071/10000000000 : ℝ)*X 0 0+(1375290767/2500000000 : ℝ)*X 0 1+(1016033211/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1067681113/2000000000 : ℝ)*X 1 0+(-729708281/5000000000 : ℝ)*X 1 1+(5080166013/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5338405661/10000000000 : ℝ)*X 2 0+(2540083049/5000000000 : ℝ)*X 2 1+(-1459416323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4027160163/10000000000 : ℝ)*X 0 0+(3375978187/10000000000 : ℝ)*X 0 1+(2371135507/5000000000 : ℝ)*X 0 2+(4027160163/10000000000 : ℝ)*X 1 0+(3375978187/10000000000 : ℝ)*X 1 1+(2371135507/5000000000 : ℝ)*X 1 2+(4027160163/10000000000 : ℝ)*X 2 0+(3375978187/10000000000 : ℝ)*X 2 1+(2371135507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1239426351/10000000000 : ℝ)*X 0 0+(635872757/1250000000 : ℝ)*X 0 1+(5494203999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226715673/10000000000 : ℝ)*X 1 0+(-522689341/5000000000 : ℝ)*X 1 1+(5494204001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2613357837/5000000000 : ℝ)*X 2 0+(1373551/2500000 : ℝ)*X 2 1+(-522689341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4028320387/10000000000 : ℝ)*X 0 0+(590018869/1250000000 : ℝ)*X 0 1+(3398562829/10000000000 : ℝ)*X 0 2+(4028320387/10000000000 : ℝ)*X 1 0+(590018869/1250000000 : ℝ)*X 1 1+(3398562829/10000000000 : ℝ)*X 1 2+(4028320387/10000000000 : ℝ)*X 2 0+(590018869/1250000000 : ℝ)*X 2 1+(3398562829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5788329309776850258797335077/1147625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27713331/3125000000000 : ℝ)*(base19) + (34843169/4000000000000 : ℝ)*(base23) + (20106903/25000000000000 : ℝ)*(upper3) + (31209727/100000000000000 : ℝ)*(upper4) + (169050209/100000000000000 : ℝ)*(upper5) + (776810083581349/50000000000000 : ℝ)*(major0) + (776810083581349/50000000000000 : ℝ)*(major1) + (776810083581349/50000000000000 : ℝ)*(major2) + (296915004554669/12500000000000 : ℝ)*(sp0) + (371144922487/15625000000 : ℝ)*(sp1) + (296915939958021/12500000000000 : ℝ)*(sp2) + (91488717675193/12500000000000 : ℝ)*(sp3) + (8354306041/100000000000000 : ℝ)*(sp4) + (254256947/12500000000000 : ℝ)*(sp7) + (731911775457121/100000000000000 : ℝ)*(f.failure) + (2375328390743393/100000000000000 : ℝ)*(f.sum) + (259311754590293/45905000000000000000000000000 : ℝ)*base65 + (6244367890386371641/4590500000000000000000000000000000 : ℝ)*base67 + (2188986482892871641/4590500000000000000000000000000000 : ℝ)*base69 + (26518925018770371641/4590500000000000000000000000000000 : ℝ)*base71 + (93154647856399/22952500000000000000000000000 : ℝ)*base73 + (31369995864062371641/4590500000000000000000000000000000 : ℝ)*base75 + (14121060903073628359/4590500000000000000000000000000000 : ℝ)*base78 + (12664364695390371641/4590500000000000000000000000000000 : ℝ)*base79 + (64164989056259/22952500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14394237/1250000000000000000000 : ℝ)*base89 + (14394237/1250000000000000000000 : ℝ)*base91 + (14394237/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25703212678511505054479238237/4590500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (366335217/50000000000000 : ℝ)*(base19) + (78630677/10000000000000 : ℝ)*(base23) + (61065521/50000000000000 : ℝ)*(upper3) + (11795331/50000000000000 : ℝ)*(lower4) + (5880499/5000000000000 : ℝ)*(upper5) + (1606164286528269/100000000000000 : ℝ)*(major0) + (1606164286528269/100000000000000 : ℝ)*(major1) + (1606164286528269/100000000000000 : ℝ)*(major2) + (2517721167/50000000000000 : ℝ)*(sp1) + (1352824073/25000000000000 : ℝ)*(sp2) + (1227831515930857/50000000000000 : ℝ)*(sp4) + (1227828631874473/50000000000000 : ℝ)*(sp5) + (613914208564663/25000000000000 : ℝ)*(sp6) + (189166338638551/25000000000000 : ℝ)*(sp7) + (189166338638551/25000000000000 : ℝ)*(f.failure) + (1227831515930857/50000000000000 : ℝ)*(f.sum) + (151489953080749/45905000000000000000000000000 : ℝ)*base65 + (10628105222142553921/9181000000000000000000000000000000 : ℝ)*base67 + (16503291443132553921/9181000000000000000000000000000000 : ℝ)*base69 + (49438302713698553921/9181000000000000000000000000000000 : ℝ)*base71 + (40759473126179/45905000000000000000000000000 : ℝ)*base73 + (15695696648229446079/9181000000000000000000000000000000 : ℝ)*base76 + (8236749311953446079/9181000000000000000000000000000000 : ℝ)*base78 + (44477418147750553921/9181000000000000000000000000000000 : ℝ)*base79 + (58719583664939/45905000000000000000000000000 : ℝ)*base81 + (272947/312500000000000000000 : ℝ)*base89 + (272947/312500000000000000000 : ℝ)*base91 + (272947/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1747_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3623/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4467/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3607/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1747_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1747_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3607/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1747_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1747_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1747_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/100 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3607/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1747_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
