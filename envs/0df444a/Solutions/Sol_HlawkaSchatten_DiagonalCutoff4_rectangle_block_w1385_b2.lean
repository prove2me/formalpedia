-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1385_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:17.845404+00:00
-- url     : https://prove2.me/submissions/6fc0c5a7-a0cf-4c5c-a1a8-93ce9a0bf96d

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
theorem support_rectangle_w1385_s6_0 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2007395561/10000000000 : ℝ)*x 0 + (5410497973/10000000000 : ℝ)*x 1 + (2622913621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007395561/10000000000 : ℝ)^4345 ≤ (12235062877967/100000000000000 : ℝ)^3321 := by
    have hnat : (2007395561 : ℕ)^4345*100000000000000^3321 ≤ 12235062877967^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007395561 10000000000 12235062877967 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410497973/10000000000 : ℝ)^4345 ≤ (11192404251503/25000000000000 : ℝ)^3321 := by
    have hnat : (5410497973 : ℕ)^4345*25000000000000^3321 ≤ 11192404251503^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410497973 10000000000 11192404251503 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622913621/5000000000 : ℝ)^4345 ≤ (42995320105167/100000000000000 : ℝ)^3321 := by
    have hnat : (2622913621 : ℕ)^4345*100000000000000^3321 ≤ 42995320105167^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622913621 5000000000 42995320105167 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2007395561/10000000000 : ℝ), (5410497973/10000000000 : ℝ), (2622913621/5000000000 : ℝ)] ![(12235062877967/100000000000000 : ℝ), (11192404251503/25000000000000 : ℝ), (42995320105167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2007395561/10000000000 : ℝ)|^4345 ≤ (12235062877967/100000000000000 : ℝ)^3321
        have hw : |(-2007395561/10000000000 : ℝ)|=(2007395561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410497973/10000000000 : ℝ)|^4345 ≤ (11192404251503/25000000000000 : ℝ)^3321
        have hw : |(5410497973/10000000000 : ℝ)|=(5410497973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622913621/5000000000 : ℝ)|^4345 ≤ (42995320105167/100000000000000 : ℝ)^3321
        have hw : |(2622913621/5000000000 : ℝ)|=(2622913621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s6_1 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668527031/1250000000 : ℝ)*x 0 + (-1045631941/5000000000 : ℝ)*x 1 + (2622913621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668527031/1250000000 : ℝ)^4345 ≤ (44096556368211/100000000000000 : ℝ)^3321 := by
    have hnat : (668527031 : ℕ)^4345*100000000000000^3321 ≤ 44096556368211^3321*1250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668527031 1250000000 44096556368211 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045631941/5000000000 : ℝ)^4345 ≤ (201689429899/1562500000000 : ℝ)^3321 := by
    have hnat : (1045631941 : ℕ)^4345*1562500000000^3321 ≤ 201689429899^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045631941 5000000000 201689429899 1562500000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622913621/5000000000 : ℝ)^4345 ≤ (42995320105167/100000000000000 : ℝ)^3321 := by
    have hnat : (2622913621 : ℕ)^4345*100000000000000^3321 ≤ 42995320105167^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622913621 5000000000 42995320105167 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668527031/1250000000 : ℝ), (-1045631941/5000000000 : ℝ), (2622913621/5000000000 : ℝ)] ![(44096556368211/100000000000000 : ℝ), (201689429899/1562500000000 : ℝ), (42995320105167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668527031/1250000000 : ℝ)|^4345 ≤ (44096556368211/100000000000000 : ℝ)^3321
        have hw : |(668527031/1250000000 : ℝ)|=(668527031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045631941/5000000000 : ℝ)|^4345 ≤ (201689429899/1562500000000 : ℝ)^3321
        have hw : |(-1045631941/5000000000 : ℝ)|=(1045631941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622913621/5000000000 : ℝ)|^4345 ≤ (42995320105167/100000000000000 : ℝ)^3321
        have hw : |(2622913621/5000000000 : ℝ)|=(2622913621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s6_2 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668527031/1250000000 : ℝ)*x 0 + (2622913621/5000000000 : ℝ)*x 1 + (-1045631941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668527031/1250000000 : ℝ)^4345 ≤ (44096556368211/100000000000000 : ℝ)^3321 := by
    have hnat : (668527031 : ℕ)^4345*100000000000000^3321 ≤ 44096556368211^3321*1250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668527031 1250000000 44096556368211 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622913621/5000000000 : ℝ)^4345 ≤ (42995320105167/100000000000000 : ℝ)^3321 := by
    have hnat : (2622913621 : ℕ)^4345*100000000000000^3321 ≤ 42995320105167^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622913621 5000000000 42995320105167 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045631941/5000000000 : ℝ)^4345 ≤ (201689429899/1562500000000 : ℝ)^3321 := by
    have hnat : (1045631941 : ℕ)^4345*1562500000000^3321 ≤ 201689429899^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045631941 5000000000 201689429899 1562500000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668527031/1250000000 : ℝ), (2622913621/5000000000 : ℝ), (-1045631941/5000000000 : ℝ)] ![(44096556368211/100000000000000 : ℝ), (42995320105167/100000000000000 : ℝ), (201689429899/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668527031/1250000000 : ℝ)|^4345 ≤ (44096556368211/100000000000000 : ℝ)^3321
        have hw : |(668527031/1250000000 : ℝ)|=(668527031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622913621/5000000000 : ℝ)|^4345 ≤ (42995320105167/100000000000000 : ℝ)^3321
        have hw : |(2622913621/5000000000 : ℝ)|=(2622913621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1045631941/5000000000 : ℝ)|^4345 ≤ (201689429899/1562500000000 : ℝ)^3321
        have hw : |(-1045631941/5000000000 : ℝ)|=(1045631941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s6_3 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157749589/5000000000 : ℝ)*x 0 + (828702107/2000000000 : ℝ)*x 1 + (112350341/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157749589/5000000000 : ℝ)^4345 ≤ (6660796876823/20000000000000 : ℝ)^3321 := by
    have hnat : (2157749589 : ℕ)^4345*20000000000000^3321 ≤ 6660796876823^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157749589 5000000000 6660796876823 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828702107/2000000000 : ℝ)^4345 ≤ (31578209738393/100000000000000 : ℝ)^3321 := by
    have hnat : (828702107 : ℕ)^4345*100000000000000^3321 ≤ 31578209738393^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828702107 2000000000 31578209738393 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112350341/250000000 : ℝ)^4345 ≤ (3511780586987/10000000000000 : ℝ)^3321 := by
    have hnat : (112350341 : ℕ)^4345*10000000000000^3321 ≤ 3511780586987^3321*250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112350341 250000000 3511780586987 10000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157749589/5000000000 : ℝ), (828702107/2000000000 : ℝ), (112350341/250000000 : ℝ)] ![(6660796876823/20000000000000 : ℝ), (31578209738393/100000000000000 : ℝ), (3511780586987/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157749589/5000000000 : ℝ)|^4345 ≤ (6660796876823/20000000000000 : ℝ)^3321
        have hw : |(2157749589/5000000000 : ℝ)|=(2157749589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828702107/2000000000 : ℝ)|^4345 ≤ (31578209738393/100000000000000 : ℝ)^3321
        have hw : |(828702107/2000000000 : ℝ)|=(828702107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112350341/250000000 : ℝ)|^4345 ≤ (3511780586987/10000000000000 : ℝ)^3321
        have hw : |(112350341/250000000 : ℝ)|=(112350341/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s6_4 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-501851849/2500000000 : ℝ)*x 0 + (5246419029/10000000000 : ℝ)*x 1 + (5409903061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501851849/2500000000 : ℝ)^4345 ≤ (12235157254237/100000000000000 : ℝ)^3321 := by
    have hnat : (501851849 : ℕ)^4345*100000000000000^3321 ≤ 12235157254237^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501851849 2500000000 12235157254237 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246419029/10000000000 : ℝ)^4345 ≤ (21500833059989/50000000000000 : ℝ)^3321 := by
    have hnat : (5246419029 : ℕ)^4345*50000000000000^3321 ≤ 21500833059989^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246419029 10000000000 21500833059989 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409903061/10000000000 : ℝ)^4345 ≤ (11190794153093/25000000000000 : ℝ)^3321 := by
    have hnat : (5409903061 : ℕ)^4345*25000000000000^3321 ≤ 11190794153093^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409903061 10000000000 11190794153093 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501851849/2500000000 : ℝ), (5246419029/10000000000 : ℝ), (5409903061/10000000000 : ℝ)] ![(12235157254237/100000000000000 : ℝ), (21500833059989/50000000000000 : ℝ), (11190794153093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501851849/2500000000 : ℝ)|^4345 ≤ (12235157254237/100000000000000 : ℝ)^3321
        have hw : |(-501851849/2500000000 : ℝ)|=(501851849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246419029/10000000000 : ℝ)|^4345 ≤ (21500833059989/50000000000000 : ℝ)^3321
        have hw : |(5246419029/10000000000 : ℝ)|=(5246419029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409903061/10000000000 : ℝ)|^4345 ≤ (11190794153093/25000000000000 : ℝ)^3321
        have hw : |(5409903061/10000000000 : ℝ)|=(5409903061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s6_5 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061119583/2000000000 : ℝ)*x 0 + (-1927187901/10000000000 : ℝ)*x 1 + (216396139/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061119583/2000000000 : ℝ)^4345 ≤ (34909905107/80000000000 : ℝ)^3321 := by
    have hnat : (1061119583 : ℕ)^4345*80000000000^3321 ≤ 34909905107^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061119583 2000000000 34909905107 80000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927187901/10000000000 : ℝ)^4345 ≤ (5799718753831/50000000000000 : ℝ)^3321 := by
    have hnat : (1927187901 : ℕ)^4345*50000000000000^3321 ≤ 5799718753831^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927187901 10000000000 5799718753831 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216396139/400000000 : ℝ)^4345 ≤ (22381590547087/50000000000000 : ℝ)^3321 := by
    have hnat : (216396139 : ℕ)^4345*50000000000000^3321 ≤ 22381590547087^3321*400000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216396139 400000000 22381590547087 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061119583/2000000000 : ℝ), (-1927187901/10000000000 : ℝ), (216396139/400000000 : ℝ)] ![(34909905107/80000000000 : ℝ), (5799718753831/50000000000000 : ℝ), (22381590547087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061119583/2000000000 : ℝ)|^4345 ≤ (34909905107/80000000000 : ℝ)^3321
        have hw : |(1061119583/2000000000 : ℝ)|=(1061119583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927187901/10000000000 : ℝ)|^4345 ≤ (5799718753831/50000000000000 : ℝ)^3321
        have hw : |(-1927187901/10000000000 : ℝ)|=(1927187901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216396139/400000000 : ℝ)|^4345 ≤ (22381590547087/50000000000000 : ℝ)^3321
        have hw : |(216396139/400000000 : ℝ)|=(216396139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s6_6 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652798883/5000000000 : ℝ)*x 0 + (5409903581/10000000000 : ℝ)*x 1 + (-963593979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652798883/5000000000 : ℝ)^4345 ≤ (10909344945097/25000000000000 : ℝ)^3321 := by
    have hnat : (2652798883 : ℕ)^4345*25000000000000^3321 ≤ 10909344945097^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652798883 5000000000 10909344945097 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409903581/10000000000 : ℝ)^4345 ≤ (5595397780211/12500000000000 : ℝ)^3321 := by
    have hnat : (5409903581 : ℕ)^4345*12500000000000^3321 ≤ 5595397780211^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409903581 10000000000 5595397780211 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963593979/5000000000 : ℝ)^4345 ≤ (11599437956519/100000000000000 : ℝ)^3321 := by
    have hnat : (963593979 : ℕ)^4345*100000000000000^3321 ≤ 11599437956519^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963593979 5000000000 11599437956519 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652798883/5000000000 : ℝ), (5409903581/10000000000 : ℝ), (-963593979/5000000000 : ℝ)] ![(10909344945097/25000000000000 : ℝ), (5595397780211/12500000000000 : ℝ), (11599437956519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652798883/5000000000 : ℝ)|^4345 ≤ (10909344945097/25000000000000 : ℝ)^3321
        have hw : |(2652798883/5000000000 : ℝ)|=(2652798883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409903581/10000000000 : ℝ)|^4345 ≤ (5595397780211/12500000000000 : ℝ)^3321
        have hw : |(5409903581/10000000000 : ℝ)|=(5409903581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-963593979/5000000000 : ℝ)|^4345 ≤ (11599437956519/100000000000000 : ℝ)^3321
        have hw : |(-963593979/5000000000 : ℝ)|=(963593979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s6_7 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172620993/400000000 : ℝ)*x 0 + (70199277/156250000 : ℝ)*x 1 + (828955261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172620993/400000000 : ℝ)^4345 ≤ (16652121669179/50000000000000 : ℝ)^3321 := by
    have hnat : (172620993 : ℕ)^4345*50000000000000^3321 ≤ 16652121669179^3321*400000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172620993 400000000 16652121669179 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70199277/156250000 : ℝ)^4345 ≤ (35104925292451/100000000000000 : ℝ)^3321 := by
    have hnat : (70199277 : ℕ)^4345*100000000000000^3321 ≤ 35104925292451^3321*156250000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70199277 156250000 35104925292451 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828955261/2000000000 : ℝ)^4345 ≤ (631816627233/2000000000000 : ℝ)^3321 := by
    have hnat : (828955261 : ℕ)^4345*2000000000000^3321 ≤ 631816627233^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828955261 2000000000 631816627233 2000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172620993/400000000 : ℝ), (70199277/156250000 : ℝ), (828955261/2000000000 : ℝ)] ![(16652121669179/50000000000000 : ℝ), (35104925292451/100000000000000 : ℝ), (631816627233/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172620993/400000000 : ℝ)|^4345 ≤ (16652121669179/50000000000000 : ℝ)^3321
        have hw : |(172620993/400000000 : ℝ)|=(172620993/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70199277/156250000 : ℝ)|^4345 ≤ (35104925292451/100000000000000 : ℝ)^3321
        have hw : |(70199277/156250000 : ℝ)|=(70199277/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828955261/2000000000 : ℝ)|^4345 ≤ (631816627233/2000000000000 : ℝ)^3321
        have hw : |(828955261/2000000000 : ℝ)|=(828955261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1385_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14733/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11241/100000 : ℝ) ^ (543/128 : ℝ) ≤ (73472809147121/781250000000000000 : ℝ) := by
    have hpowers : (11241/100000 : ℝ)^543 ≤ (73472809147121/781250000000000000 : ℝ)^128 := by
      have hnat : (11241 : ℕ)^543*781250000000000000^128 ≤ 73472809147121^128*100000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11241 100000 73472809147121 781250000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11241/100000 : ℝ)) (X := (73472809147121/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14739/100000 : ℝ) ^ (543/128 : ℝ) ≤ (14840735607979527/50000000000000000000 : ℝ) := by
    have hpowers : (14739/100000 : ℝ)^543 ≤ (14840735607979527/50000000000000000000 : ℝ)^128 := by
      have hnat : (14739 : ℕ)^543*50000000000000000000^128 ≤ 14840735607979527^128*100000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14739 100000 14840735607979527 50000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14739/100000 : ℝ)) (X := (14840735607979527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (390698472809147121/390625000000000000 : ℝ) ≤ (5000221674399937/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (390698472809147121/390625000000000000 : ℝ)^128 ≤ (5000221674399937/5000000000000000 : ℝ)^543 := by
      have hnat : (390698472809147121 : ℕ)^128*5000000000000000^543 ≤ 5000221674399937^543*390625000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390698472809147121 390625000000000000 5000221674399937 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000221674399937/5000000000000000 : ℝ)) (X := (390698472809147121/390625000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019542995393395271/50000000000000000000 : ℝ) ≤ (2000184245294091/2000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (50019542995393395271/50000000000000000000 : ℝ)^128 ≤ (2000184245294091/2000000000000000 : ℝ)^543 := by
      have hnat : (50019542995393395271 : ℕ)^128*2000000000000000^543 ≤ 2000184245294091^543*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019542995393395271 50000000000000000000 2000184245294091 2000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000184245294091/2000000000000000 : ℝ)) (X := (50019542995393395271/50000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014840735607979527/25000000000000000000 : ℝ) ≤ (2500349776035259/2500000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (25014840735607979527/25000000000000000000 : ℝ)^128 ≤ (2500349776035259/2500000000000000 : ℝ)^543 := by
      have hnat : (25014840735607979527 : ℕ)^128*2500000000000000^543 ≤ 2500349776035259^543*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014840735607979527 25000000000000000000 2500349776035259 2500000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500349776035259/2500000000000000 : ℝ)) (X := (25014840735607979527/25000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(73472809147121/781250000000000000 : ℝ) ≤ ((1165693572943731907/1166000000000000000 : ℝ)+2*(477877670581/349800000000000 : ℝ)*(11241/100000 : ℝ))^(543/128 : ℝ) := by
    rw [show (1165693572943731907/1166000000000000000 : ℝ)+2*(477877670581/349800000000000 : ℝ)*(11241/100000 : ℝ)=(5000221674399937/5000000000000000 : ℝ) by norm_num, show 1+2*(73472809147121/781250000000000000 : ℝ)=(390698472809147121/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14840735607979527/50000000000000000000 : ℝ)+(73472809147121/781250000000000000 : ℝ) ≤ ((1165693572943731907/1166000000000000000 : ℝ)+(477877670581/349800000000000 : ℝ)*((14739/100000 : ℝ)+(11241/100000 : ℝ)))^(543/128 : ℝ) := by
    rw [show (1165693572943731907/1166000000000000000 : ℝ)+(477877670581/349800000000000 : ℝ)*((14739/100000 : ℝ)+(11241/100000 : ℝ))=(2000184245294091/2000000000000000 : ℝ) by norm_num, show 1+(14840735607979527/50000000000000000000 : ℝ)+(73472809147121/781250000000000000 : ℝ)=(50019542995393395271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14840735607979527/50000000000000000000 : ℝ) ≤ ((1165693572943731907/1166000000000000000 : ℝ)+2*(477877670581/349800000000000 : ℝ)*(14739/100000 : ℝ))^(543/128 : ℝ) := by
    rw [show (1165693572943731907/1166000000000000000 : ℝ)+2*(477877670581/349800000000000 : ℝ)*(14739/100000 : ℝ)=(2500349776035259/2500000000000000 : ℝ) by norm_num, show 1+2*(14840735607979527/50000000000000000000 : ℝ)=(25014840735607979527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1165693572943731907/1166000000000000000 : ℝ)*(X 1 0+X 2 0)+(477877670581/349800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (1165693572943731907/1166000000000000000 : ℝ)) (alpha := (477877670581/349800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1165693572943731907/1166000000000000000 : ℝ)*(X 0 1+X 2 1)+(477877670581/349800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (1165693572943731907/1166000000000000000 : ℝ)) (alpha := (477877670581/349800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1165693572943731907/1166000000000000000 : ℝ)*(X 0 2+X 1 2)+(477877670581/349800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (1165693572943731907/1166000000000000000 : ℝ)) (alpha := (477877670581/349800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2007395561/10000000000 : ℝ)*X 0 0+(5410497973/10000000000 : ℝ)*X 0 1+(2622913621/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668527031/1250000000 : ℝ)*X 1 0+(-1045631941/5000000000 : ℝ)*X 1 1+(2622913621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668527031/1250000000 : ℝ)*X 2 0+(2622913621/5000000000 : ℝ)*X 2 1+(-1045631941/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157749589/5000000000 : ℝ)*X 0 0+(828702107/2000000000 : ℝ)*X 0 1+(112350341/250000000 : ℝ)*X 0 2+(2157749589/5000000000 : ℝ)*X 1 0+(828702107/2000000000 : ℝ)*X 1 1+(112350341/250000000 : ℝ)*X 1 2+(2157749589/5000000000 : ℝ)*X 2 0+(828702107/2000000000 : ℝ)*X 2 1+(112350341/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-501851849/2500000000 : ℝ)*X 0 0+(5246419029/10000000000 : ℝ)*X 0 1+(5409903061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061119583/2000000000 : ℝ)*X 1 0+(-1927187901/10000000000 : ℝ)*X 1 1+(216396139/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652798883/5000000000 : ℝ)*X 2 0+(5409903581/10000000000 : ℝ)*X 2 1+(-963593979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172620993/400000000 : ℝ)*X 0 0+(70199277/156250000 : ℝ)*X 0 1+(828955261/2000000000 : ℝ)*X 0 2+(172620993/400000000 : ℝ)*X 1 0+(70199277/156250000 : ℝ)*X 1 1+(828955261/2000000000 : ℝ)*X 1 2+(172620993/400000000 : ℝ)*X 2 0+(70199277/156250000 : ℝ)*X 2 1+(828955261/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125810740234062080667118791/11660000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (997065479/50000000000000 : ℝ)*(base19) + (29044129/1562500000000 : ℝ)*(base23) + (72364951/100000000000000 : ℝ)*(lower2) + (269817651/100000000000000 : ℝ)*(upper3) + (85361669/50000000000000 : ℝ)*(upper5) + (892589107210671/20000000000000 : ℝ)*(major0) + (892589107210671/20000000000000 : ℝ)*(major1) + (892589107210671/20000000000000 : ℝ)*(major2) + (607276775540663/10000000000000 : ℝ)*(sp0) + (6072807097449471/100000000000000 : ℝ)*(sp1) + (6072807232756173/100000000000000 : ℝ)*(sp2) + (2853060611096859/100000000000000 : ℝ)*(sp3) + (41336173799/100000000000000 : ℝ)*(sp4) + (10504882317/50000000000000 : ℝ)*(sp7) + (1426540810430747/50000000000000 : ℝ)*(f.failure) + (6072809091580429/100000000000000 : ℝ)*(f.sum) + (8504119475029/1166000000000000000000000000 : ℝ)*base65 + (141532666036789597/23320000000000000000000000000000 : ℝ)*base67 + (68811869552530403/23320000000000000000000000000000 : ℝ)*base70 + (305497240163450403/23320000000000000000000000000000 : ℝ)*base72 + (2563670618247/1166000000000000000000000000 : ℝ)*base73 + (24216839187909597/23320000000000000000000000000000 : ℝ)*base75 + (121262106482170403/23320000000000000000000000000000 : ℝ)*base78 + (104178110643810403/23320000000000000000000000000000 : ℝ)*base80 + (321307037687/1166000000000000000000000000 : ℝ)*base82 + (29932587/2500000000000000000000 : ℝ)*base89 + (29932587/2500000000000000000000 : ℝ)*base91 + (29932587/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (456540277977079059926313/132500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28473247/10000000000000 : ℝ)*(base19) + (440093677/100000000000000 : ℝ)*(base23) + (107947469/50000000000000 : ℝ)*(upper3) + (38572231/25000000000000 : ℝ)*(lower4) + (35070553/20000000000000 : ℝ)*(upper5) + (112381846687561/2500000000000 : ℝ)*(major0) + (112381846687561/2500000000000 : ℝ)*(major1) + (112381846687561/2500000000000 : ℝ)*(major2) + (10241306267/100000000000000 : ℝ)*(sp1) + (7382539487/50000000000000 : ℝ)*(sp2) + (6116799072583581/100000000000000 : ℝ)*(sp4) + (1529197136636211/25000000000000 : ℝ)*(sp5) + (611678386741093/10000000000000 : ℝ)*(sp6) + (1436874273784197/50000000000000 : ℝ)*(sp7) + (1436874273784197/50000000000000 : ℝ)*(f.failure) + (6116799072583581/100000000000000 : ℝ)*(f.sum) + (312922283329/79500000000000000000000000 : ℝ)*base65 + (4107072170346229/795000000000000000000000000000 : ℝ)*base68 + (4164002064696229/795000000000000000000000000000 : ℝ)*base70 + (4484515787121229/795000000000000000000000000000 : ℝ)*base72 + (175738997689/79500000000000000000000000 : ℝ)*base73 + (7234782637731229/795000000000000000000000000000 : ℝ)*base76 + (4061516524641229/795000000000000000000000000000 : ℝ)*base78 + (4063177985601229/795000000000000000000000000000 : ℝ)*base80 + (128809013383/79500000000000000000000000 : ℝ)*base81 + (14170037/2500000000000000000000 : ℝ)*base89 + (14170037/2500000000000000000000 : ℝ)*base91 + (14170037/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1385_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1385_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1385_s7_0 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2007402073/10000000000 : ℝ)*x 0 + (5410454289/10000000000 : ℝ)*x 1 + (5245866501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007402073/10000000000 : ℝ)^4345 ≤ (12235114806823/100000000000000 : ℝ)^3321 := by
    have hnat : (2007402073 : ℕ)^4345*100000000000000^3321 ≤ 12235114806823^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007402073 10000000000 12235114806823 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410454289/10000000000 : ℝ)^4345 ≤ (44769144084681/100000000000000 : ℝ)^3321 := by
    have hnat : (5410454289 : ℕ)^4345*100000000000000^3321 ≤ 44769144084681^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410454289 10000000000 44769144084681 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245866501/10000000000 : ℝ)^4345 ≤ (42995741091349/100000000000000 : ℝ)^3321 := by
    have hnat : (5245866501 : ℕ)^4345*100000000000000^3321 ≤ 42995741091349^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245866501 10000000000 42995741091349 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2007402073/10000000000 : ℝ), (5410454289/10000000000 : ℝ), (5245866501/10000000000 : ℝ)] ![(12235114806823/100000000000000 : ℝ), (44769144084681/100000000000000 : ℝ), (42995741091349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2007402073/10000000000 : ℝ)|^4345 ≤ (12235114806823/100000000000000 : ℝ)^3321
        have hw : |(-2007402073/10000000000 : ℝ)|=(2007402073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410454289/10000000000 : ℝ)|^4345 ≤ (44769144084681/100000000000000 : ℝ)^3321
        have hw : |(5410454289/10000000000 : ℝ)|=(5410454289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245866501/10000000000 : ℝ)|^4345 ≤ (42995741091349/100000000000000 : ℝ)^3321
        have hw : |(5245866501/10000000000 : ℝ)|=(5245866501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s7_1 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348204591/10000000000 : ℝ)*x 0 + (-2091227353/10000000000 : ℝ)*x 1 + (2622933239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348204591/10000000000 : ℝ)^4345 ≤ (22048215309789/50000000000000 : ℝ)^3321 := by
    have hnat : (5348204591 : ℕ)^4345*50000000000000^3321 ≤ 22048215309789^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348204591 10000000000 22048215309789 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091227353/10000000000 : ℝ)^4345 ≤ (12907828520479/100000000000000 : ℝ)^3321 := by
    have hnat : (2091227353 : ℕ)^4345*100000000000000^3321 ≤ 12907828520479^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091227353 10000000000 12907828520479 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622933239/5000000000 : ℝ)^4345 ≤ (42995740844713/100000000000000 : ℝ)^3321 := by
    have hnat : (2622933239 : ℕ)^4345*100000000000000^3321 ≤ 42995740844713^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622933239 5000000000 42995740844713 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348204591/10000000000 : ℝ), (-2091227353/10000000000 : ℝ), (2622933239/5000000000 : ℝ)] ![(22048215309789/50000000000000 : ℝ), (12907828520479/100000000000000 : ℝ), (42995740844713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348204591/10000000000 : ℝ)|^4345 ≤ (22048215309789/50000000000000 : ℝ)^3321
        have hw : |(5348204591/10000000000 : ℝ)|=(5348204591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091227353/10000000000 : ℝ)|^4345 ≤ (12907828520479/100000000000000 : ℝ)^3321
        have hw : |(-2091227353/10000000000 : ℝ)|=(2091227353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622933239/5000000000 : ℝ)|^4345 ≤ (42995740844713/100000000000000 : ℝ)^3321
        have hw : |(2622933239/5000000000 : ℝ)|=(2622933239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s7_2 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348204543/10000000000 : ℝ)*x 0 + (1311466627/2500000000 : ℝ)*x 1 + (-1045613689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348204543/10000000000 : ℝ)^4345 ≤ (44096430101783/100000000000000 : ℝ)^3321 := by
    have hnat : (5348204543 : ℕ)^4345*100000000000000^3321 ≤ 44096430101783^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348204543 10000000000 44096430101783 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311466627/2500000000 : ℝ)^4345 ≤ (42995741166413/100000000000000 : ℝ)^3321 := by
    have hnat : (1311466627 : ℕ)^4345*100000000000000^3321 ≤ 42995741166413^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311466627 2500000000 42995741166413 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045613689/5000000000 : ℝ)^4345 ≤ (201684823787/1562500000000 : ℝ)^3321 := by
    have hnat : (1045613689 : ℕ)^4345*1562500000000^3321 ≤ 201684823787^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045613689 5000000000 201684823787 1562500000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348204543/10000000000 : ℝ), (1311466627/2500000000 : ℝ), (-1045613689/5000000000 : ℝ)] ![(44096430101783/100000000000000 : ℝ), (42995741166413/100000000000000 : ℝ), (201684823787/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348204543/10000000000 : ℝ)|^4345 ≤ (44096430101783/100000000000000 : ℝ)^3321
        have hw : |(5348204543/10000000000 : ℝ)|=(5348204543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311466627/2500000000 : ℝ)|^4345 ≤ (42995741166413/100000000000000 : ℝ)^3321
        have hw : |(1311466627/2500000000 : ℝ)|=(1311466627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1045613689/5000000000 : ℝ)|^4345 ≤ (201684823787/1562500000000 : ℝ)^3321
        have hw : |(-1045613689/5000000000 : ℝ)|=(1045613689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s7_3 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539437749/1250000000 : ℝ)*x 0 + (414359853/1000000000 : ℝ)*x 1 + (56174063/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539437749/1250000000 : ℝ)^4345 ≤ (4163001599583/12500000000000 : ℝ)^3321 := by
    have hnat : (539437749 : ℕ)^4345*12500000000000^3321 ≤ 4163001599583^3321*1250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539437749 1250000000 4163001599583 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414359853/1000000000 : ℝ)^4345 ≤ (31579087141929/100000000000000 : ℝ)^3321 := by
    have hnat : (414359853 : ℕ)^4345*100000000000000^3321 ≤ 31579087141929^3321*1000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414359853 1000000000 31579087141929 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56174063/125000000 : ℝ)^4345 ≤ (7023380008143/20000000000000 : ℝ)^3321 := by
    have hnat : (56174063 : ℕ)^4345*20000000000000^3321 ≤ 7023380008143^3321*125000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56174063 125000000 7023380008143 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539437749/1250000000 : ℝ), (414359853/1000000000 : ℝ), (56174063/125000000 : ℝ)] ![(4163001599583/12500000000000 : ℝ), (31579087141929/100000000000000 : ℝ), (7023380008143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539437749/1250000000 : ℝ)|^4345 ≤ (4163001599583/12500000000000 : ℝ)^3321
        have hw : |(539437749/1250000000 : ℝ)|=(539437749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(414359853/1000000000 : ℝ)|^4345 ≤ (31579087141929/100000000000000 : ℝ)^3321
        have hw : |(414359853/1000000000 : ℝ)|=(414359853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56174063/125000000 : ℝ)|^4345 ≤ (7023380008143/20000000000000 : ℝ)^3321
        have hw : |(56174063/125000000 : ℝ)|=(56174063/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s7_4 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2007413877/10000000000 : ℝ)*x 0 + (2623228793/5000000000 : ℝ)*x 1 + (5409860093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007413877/10000000000 : ℝ)^4345 ≤ (12235208935983/100000000000000 : ℝ)^3321 := by
    have hnat : (2007413877 : ℕ)^4345*100000000000000^3321 ≤ 12235208935983^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007413877 10000000000 12235208935983 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623228793/5000000000 : ℝ)^4345 ≤ (1720083183711/4000000000000 : ℝ)^3321 := by
    have hnat : (2623228793 : ℕ)^4345*4000000000000^3321 ≤ 1720083183711^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623228793 5000000000 1720083183711 4000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409860093/10000000000 : ℝ)^4345 ≤ (2797669466137/6250000000000 : ℝ)^3321 := by
    have hnat : (5409860093 : ℕ)^4345*6250000000000^3321 ≤ 2797669466137^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409860093 10000000000 2797669466137 6250000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2007413877/10000000000 : ℝ), (2623228793/5000000000 : ℝ), (5409860093/10000000000 : ℝ)] ![(12235208935983/100000000000000 : ℝ), (1720083183711/4000000000000 : ℝ), (2797669466137/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2007413877/10000000000 : ℝ)|^4345 ≤ (12235208935983/100000000000000 : ℝ)^3321
        have hw : |(-2007413877/10000000000 : ℝ)|=(2007413877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623228793/5000000000 : ℝ)|^4345 ≤ (1720083183711/4000000000000 : ℝ)^3321
        have hw : |(2623228793/5000000000 : ℝ)|=(2623228793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409860093/10000000000 : ℝ)|^4345 ≤ (2797669466137/6250000000000 : ℝ)^3321
        have hw : |(5409860093/10000000000 : ℝ)|=(5409860093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s7_5 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607903/10000000000 : ℝ)*x 0 + (-48180847/250000000 : ℝ)*x 1 + (5409860101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607903/10000000000 : ℝ)^4345 ≤ (43637488862823/100000000000000 : ℝ)^3321 := by
    have hnat : (5305607903 : ℕ)^4345*100000000000000^3321 ≤ 43637488862823^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607903 10000000000 43637488862823 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48180847/250000000 : ℝ)^4345 ≤ (5799899789811/50000000000000 : ℝ)^3321 := by
    have hnat : (48180847 : ℕ)^4345*50000000000000^3321 ≤ 5799899789811^3321*250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48180847 250000000 5799899789811 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409860101/10000000000 : ℝ)^4345 ≤ (11190677886199/25000000000000 : ℝ)^3321 := by
    have hnat : (5409860101 : ℕ)^4345*25000000000000^3321 ≤ 11190677886199^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409860101 10000000000 11190677886199 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607903/10000000000 : ℝ), (-48180847/250000000 : ℝ), (5409860101/10000000000 : ℝ)] ![(43637488862823/100000000000000 : ℝ), (5799899789811/50000000000000 : ℝ), (11190677886199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607903/10000000000 : ℝ)|^4345 ≤ (43637488862823/100000000000000 : ℝ)^3321
        have hw : |(5305607903/10000000000 : ℝ)|=(5305607903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48180847/250000000 : ℝ)|^4345 ≤ (5799899789811/50000000000000 : ℝ)^3321
        have hw : |(-48180847/250000000 : ℝ)|=(48180847/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409860101/10000000000 : ℝ)|^4345 ≤ (11190677886199/25000000000000 : ℝ)^3321
        have hw : |(5409860101/10000000000 : ℝ)|=(5409860101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s7_6 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652804021/5000000000 : ℝ)*x 0 + (2704930031/5000000000 : ℝ)*x 1 + (-120452109/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652804021/5000000000 : ℝ)^4345 ≤ (43637490358577/100000000000000 : ℝ)^3321 := by
    have hnat : (2652804021 : ℕ)^4345*100000000000000^3321 ≤ 43637490358577^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652804021 5000000000 43637490358577 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704930031/5000000000 : ℝ)^4345 ≤ (44762711122599/100000000000000 : ℝ)^3321 := by
    have hnat : (2704930031 : ℕ)^4345*100000000000000^3321 ≤ 44762711122599^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704930031 5000000000 44762711122599 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120452109/625000000 : ℝ)^4345 ≤ (2319959701731/20000000000000 : ℝ)^3321 := by
    have hnat : (120452109 : ℕ)^4345*20000000000000^3321 ≤ 2319959701731^3321*625000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120452109 625000000 2319959701731 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652804021/5000000000 : ℝ), (2704930031/5000000000 : ℝ), (-120452109/625000000 : ℝ)] ![(43637490358577/100000000000000 : ℝ), (44762711122599/100000000000000 : ℝ), (2319959701731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652804021/5000000000 : ℝ)|^4345 ≤ (43637490358577/100000000000000 : ℝ)^3321
        have hw : |(2652804021/5000000000 : ℝ)|=(2652804021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704930031/5000000000 : ℝ)|^4345 ≤ (44762711122599/100000000000000 : ℝ)^3321
        have hw : |(2704930031/5000000000 : ℝ)|=(2704930031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120452109/625000000 : ℝ)|^4345 ≤ (2319959701731/20000000000000 : ℝ)^3321
        have hw : |(-120452109/625000000 : ℝ)|=(120452109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s7_7 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4315527133/10000000000 : ℝ)*x 0 + (2246333383/5000000000 : ℝ)*x 1 + (2072431559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315527133/10000000000 : ℝ)^4345 ≤ (33304266641941/100000000000000 : ℝ)^3321 := by
    have hnat : (4315527133 : ℕ)^4345*100000000000000^3321 ≤ 33304266641941^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315527133 10000000000 33304266641941 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246333383/5000000000 : ℝ)^4345 ≤ (2194002267919/6250000000000 : ℝ)^3321 := by
    have hnat : (2246333383 : ℕ)^4345*6250000000000^3321 ≤ 2194002267919^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246333383 5000000000 2194002267919 6250000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072431559/5000000000 : ℝ)^4345 ≤ (31591697060879/100000000000000 : ℝ)^3321 := by
    have hnat : (2072431559 : ℕ)^4345*100000000000000^3321 ≤ 31591697060879^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072431559 5000000000 31591697060879 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315527133/10000000000 : ℝ), (2246333383/5000000000 : ℝ), (2072431559/5000000000 : ℝ)] ![(33304266641941/100000000000000 : ℝ), (2194002267919/6250000000000 : ℝ), (31591697060879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315527133/10000000000 : ℝ)|^4345 ≤ (33304266641941/100000000000000 : ℝ)^3321
        have hw : |(4315527133/10000000000 : ℝ)|=(4315527133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246333383/5000000000 : ℝ)|^4345 ≤ (2194002267919/6250000000000 : ℝ)^3321
        have hw : |(2246333383/5000000000 : ℝ)|=(2246333383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072431559/5000000000 : ℝ)|^4345 ≤ (31591697060879/100000000000000 : ℝ)^3321
        have hw : |(2072431559/5000000000 : ℝ)|=(2072431559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1385_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11247/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3683/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5623/50000 : ℝ) ^ (543/128 : ℝ) ≤ (4711139002627017/50000000000000000000 : ℝ) := by
    have hpowers : (5623/50000 : ℝ)^543 ≤ (4711139002627017/50000000000000000000 : ℝ)^128 := by
      have hnat : (5623 : ℕ)^543*50000000000000000000^128 ≤ 4711139002627017^128*50000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5623 50000 4711139002627017 50000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5623/50000 : ℝ)) (X := (4711139002627017/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14733/100000 : ℝ) ^ (543/128 : ℝ) ≤ (7407561850597767/25000000000000000000 : ℝ) := by
    have hpowers : (14733/100000 : ℝ)^543 ≤ (7407561850597767/25000000000000000000 : ℝ)^128 := by
      have hnat : (14733 : ℕ)^543*25000000000000000000^128 ≤ 7407561850597767^128*100000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14733 100000 7407561850597767 25000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14733/100000 : ℝ)) (X := (7407561850597767/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004711139002627017/25000000000000000000 : ℝ) ≤ (2500111046477371/2500000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (25004711139002627017/25000000000000000000 : ℝ)^128 ≤ (2500111046477371/2500000000000000 : ℝ)^543 := by
      have hnat : (25004711139002627017 : ℕ)^128*2500000000000000^543 ≤ 2500111046477371^543*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004711139002627017 25000000000000000000 2500111046477371 2500000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111046477371/2500000000000000 : ℝ)) (X := (25004711139002627017/25000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019526262703822551/50000000000000000000 : ℝ) ≤ (10000920437835111/10000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (50019526262703822551/50000000000000000000 : ℝ)^128 ≤ (10000920437835111/10000000000000000 : ℝ)^543 := by
      have hnat : (50019526262703822551 : ℕ)^128*10000000000000000^543 ≤ 10000920437835111^543*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019526262703822551 50000000000000000000 10000920437835111 10000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000920437835111/10000000000000000 : ℝ)) (X := (50019526262703822551/50000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507407561850597767/12500000000000000000 : ℝ) ≤ (5000698344880369/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (12507407561850597767/12500000000000000000 : ℝ)^128 ≤ (5000698344880369/5000000000000000 : ℝ)^543 := by
      have hnat : (12507407561850597767 : ℕ)^128*5000000000000000^543 ≤ 5000698344880369^543*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507407561850597767 12500000000000000000 5000698344880369 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000698344880369/5000000000000000 : ℝ)) (X := (12507407561850597767/12500000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4711139002627017/50000000000000000000 : ℝ) ≤ ((1089401156811099007/1089687500000000000 : ℝ)+2*(476251925627/348700000000000 : ℝ)*(5623/50000 : ℝ))^(543/128 : ℝ) := by
    rw [show (1089401156811099007/1089687500000000000 : ℝ)+2*(476251925627/348700000000000 : ℝ)*(5623/50000 : ℝ)=(2500111046477371/2500000000000000 : ℝ) by norm_num, show 1+2*(4711139002627017/50000000000000000000 : ℝ)=(25004711139002627017/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7407561850597767/25000000000000000000 : ℝ)+(4711139002627017/50000000000000000000 : ℝ) ≤ ((1089401156811099007/1089687500000000000 : ℝ)+(476251925627/348700000000000 : ℝ)*((14733/100000 : ℝ)+(5623/50000 : ℝ)))^(543/128 : ℝ) := by
    rw [show (1089401156811099007/1089687500000000000 : ℝ)+(476251925627/348700000000000 : ℝ)*((14733/100000 : ℝ)+(5623/50000 : ℝ))=(10000920437835111/10000000000000000 : ℝ) by norm_num, show 1+(7407561850597767/25000000000000000000 : ℝ)+(4711139002627017/50000000000000000000 : ℝ)=(50019526262703822551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7407561850597767/25000000000000000000 : ℝ) ≤ ((1089401156811099007/1089687500000000000 : ℝ)+2*(476251925627/348700000000000 : ℝ)*(14733/100000 : ℝ))^(543/128 : ℝ) := by
    rw [show (1089401156811099007/1089687500000000000 : ℝ)+2*(476251925627/348700000000000 : ℝ)*(14733/100000 : ℝ)=(5000698344880369/5000000000000000 : ℝ) by norm_num, show 1+2*(7407561850597767/25000000000000000000 : ℝ)=(12507407561850597767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1089401156811099007/1089687500000000000 : ℝ)*(X 1 0+X 2 0)+(476251925627/348700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (1089401156811099007/1089687500000000000 : ℝ)) (alpha := (476251925627/348700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1089401156811099007/1089687500000000000 : ℝ)*(X 0 1+X 2 1)+(476251925627/348700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (1089401156811099007/1089687500000000000 : ℝ)) (alpha := (476251925627/348700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1089401156811099007/1089687500000000000 : ℝ)*(X 0 2+X 1 2)+(476251925627/348700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (1089401156811099007/1089687500000000000 : ℝ)) (alpha := (476251925627/348700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2007402073/10000000000 : ℝ)*X 0 0+(5410454289/10000000000 : ℝ)*X 0 1+(5245866501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348204591/10000000000 : ℝ)*X 1 0+(-2091227353/10000000000 : ℝ)*X 1 1+(2622933239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348204543/10000000000 : ℝ)*X 2 0+(1311466627/2500000000 : ℝ)*X 2 1+(-1045613689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539437749/1250000000 : ℝ)*X 0 0+(414359853/1000000000 : ℝ)*X 0 1+(56174063/125000000 : ℝ)*X 0 2+(539437749/1250000000 : ℝ)*X 1 0+(414359853/1000000000 : ℝ)*X 1 1+(56174063/125000000 : ℝ)*X 1 2+(539437749/1250000000 : ℝ)*X 2 0+(414359853/1000000000 : ℝ)*X 2 1+(56174063/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2007413877/10000000000 : ℝ)*X 0 0+(2623228793/5000000000 : ℝ)*X 0 1+(5409860093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305607903/10000000000 : ℝ)*X 1 0+(-48180847/250000000 : ℝ)*X 1 1+(5409860101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652804021/5000000000 : ℝ)*X 2 0+(2704930031/5000000000 : ℝ)*X 2 1+(-120452109/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315527133/10000000000 : ℝ)*X 0 0+(2246333383/5000000000 : ℝ)*X 0 1+(2072431559/5000000000 : ℝ)*X 0 2+(4315527133/10000000000 : ℝ)*X 1 0+(2246333383/5000000000 : ℝ)*X 1 1+(2072431559/5000000000 : ℝ)*X 1 2+(4315527133/10000000000 : ℝ)*X 2 0+(2246333383/5000000000 : ℝ)*X 2 1+(2072431559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9173499565412261933058249/990625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86139543/5000000000000 : ℝ)*(base19) + (48715249/3125000000000 : ℝ)*(base23) + (58494501/100000000000000 : ℝ)*(lower2) + (218699087/100000000000000 : ℝ)*(upper3) + (98393197/100000000000000 : ℝ)*(upper5) + (893037504533647/20000000000000 : ℝ)*(major0) + (893037504533647/20000000000000 : ℝ)*(major1) + (893037504533647/20000000000000 : ℝ)*(major2) + (6075824098359789/100000000000000 : ℝ)*(sp0) + (6075858130881413/100000000000000 : ℝ)*(sp1) + (1215171658956861/20000000000000 : ℝ)*(sp2) + (11417985361801/400000000000 : ℝ)*(sp3) + (8938828121/25000000000000 : ℝ)*(sp4) + (9271268387/50000000000000 : ℝ)*(sp7) + (178407180186689/6250000000000 : ℝ)*(f.failure) + (6075859853672273/100000000000000 : ℝ)*(f.sum) + (90702281387/31700000000000000000000000 : ℝ)*base65 + (1459307026914441/495312500000000000000000000000 : ℝ)*base67 + (4923266771495691/495312500000000000000000000000 : ℝ)*base69 + (1077133810145691/495312500000000000000000000000 : ℝ)*base71 + (5093272419/1238281250000000000000000 : ℝ)*base73 + (4939825156050757/990625000000000000000000000000 : ℝ)*base75 + (5374994781014441/495312500000000000000000000000 : ℝ)*base77 + (15855118274094507/990625000000000000000000000000 : ℝ)*base79 + (143967734687/63400000000000000000000000 : ℝ)*base82 + (295769/312500000000000000000 : ℝ)*base89 + (295769/312500000000000000000 : ℝ)*base91 + (295769/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9904194723384489270097749/5448437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (337186743/100000000000000 : ℝ)*(base19) + (28623351/5000000000000 : ℝ)*(base23) + (105799591/100000000000000 : ℝ)*(lower1) + (53869739/100000000000000 : ℝ)*(upper3) + (6644207/50000000000000 : ℝ)*(lower4) + (31242851/50000000000000 : ℝ)*(upper5) + (449751765401119/10000000000000 : ℝ)*(major0) + (449751765401119/10000000000000 : ℝ)*(major1) + (449751765401119/10000000000000 : ℝ)*(major2) + (310778159/5000000000000 : ℝ)*(sp2) + (1529963071773707/25000000000000 : ℝ)*(sp4) + (1223970389981617/20000000000000 : ℝ)*(sp5) + (6119845499064629/100000000000000 : ℝ)*(sp6) + (287518296033403/10000000000000 : ℝ)*(sp7) + (287518296033403/10000000000000 : ℝ)*(f.failure) + (1529963071773707/25000000000000 : ℝ)*(f.sum) + (272674215983/871750000000000000000000000 : ℝ)*base66 + (112855688872054021/5448437500000000000000000000000 : ℝ)*base68 + (35519980505447771/5448437500000000000000000000000 : ℝ)*base70 + (1408167456791792417/10896875000000000000000000000000 : ℝ)*base72 + (9395039461717/1743500000000000000000000000 : ℝ)*base74 + (1664233796473645083/10896875000000000000000000000000 : ℝ)*base75 + (49072993871304021/5448437500000000000000000000000 : ℝ)*base78 + (1211292391308927/2724218750000000000000000000000 : ℝ)*base79 + (16743883843981/1743500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5519563/500000000000000000000 : ℝ)*base89 + (5519563/500000000000000000000 : ℝ)*base91 + (5519563/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1385_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1385_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1385_box_0 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-230435827/1250000000 : ℝ)*x 0 + (2694064839/5000000000 : ℝ)*x 1 + (1347032429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230435827/1250000000 : ℝ)^4345 ≤ (10944773810267/100000000000000 : ℝ)^3321 := by
    have hnat : (230435827 : ℕ)^4345*100000000000000^3321 ≤ 10944773810267^3321*1250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230435827 1250000000 10944773810267 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694064839/5000000000 : ℝ)^4345 ≤ (4452761288301/10000000000000 : ℝ)^3321 := by
    have hnat : (2694064839 : ℕ)^4345*10000000000000^3321 ≤ 4452761288301^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694064839 5000000000 4452761288301 10000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347032429/2500000000 : ℝ)^4345 ≤ (2782975830867/6250000000000 : ℝ)^3321 := by
    have hnat : (1347032429 : ℕ)^4345*6250000000000^3321 ≤ 2782975830867^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347032429 2500000000 2782975830867 6250000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230435827/1250000000 : ℝ), (2694064839/5000000000 : ℝ), (1347032429/2500000000 : ℝ)] ![(10944773810267/100000000000000 : ℝ), (4452761288301/10000000000000 : ℝ), (2782975830867/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230435827/1250000000 : ℝ)|^4345 ≤ (10944773810267/100000000000000 : ℝ)^3321
        have hw : |(-230435827/1250000000 : ℝ)|=(230435827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694064839/5000000000 : ℝ)|^4345 ≤ (4452761288301/10000000000000 : ℝ)^3321
        have hw : |(2694064839/5000000000 : ℝ)|=(2694064839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347032429/2500000000 : ℝ)|^4345 ≤ (2782975830867/6250000000000 : ℝ)^3321
        have hw : |(1347032429/2500000000 : ℝ)|=(1347032429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_1 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285681069/10000000000 : ℝ)*x 0 + (-1984045763/10000000000 : ℝ)*x 1 + (1347032521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285681069/10000000000 : ℝ)^4345 ≤ (21711591995203/50000000000000 : ℝ)^3321 := by
    have hnat : (5285681069 : ℕ)^4345*50000000000000^3321 ≤ 21711591995203^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285681069 10000000000 21711591995203 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984045763/10000000000 : ℝ)^4345 ≤ (6024599357539/50000000000000 : ℝ)^3321 := by
    have hnat : (1984045763 : ℕ)^4345*50000000000000^3321 ≤ 6024599357539^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984045763 10000000000 6024599357539 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347032521/2500000000 : ℝ)^4345 ≤ (8905523454549/20000000000000 : ℝ)^3321 := by
    have hnat : (1347032521 : ℕ)^4345*20000000000000^3321 ≤ 8905523454549^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347032521 2500000000 8905523454549 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285681069/10000000000 : ℝ), (-1984045763/10000000000 : ℝ), (1347032521/2500000000 : ℝ)] ![(21711591995203/50000000000000 : ℝ), (6024599357539/50000000000000 : ℝ), (8905523454549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285681069/10000000000 : ℝ)|^4345 ≤ (21711591995203/50000000000000 : ℝ)^3321
        have hw : |(5285681069/10000000000 : ℝ)|=(5285681069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1984045763/10000000000 : ℝ)|^4345 ≤ (6024599357539/50000000000000 : ℝ)^3321
        have hw : |(-1984045763/10000000000 : ℝ)|=(1984045763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347032521/2500000000 : ℝ)|^4345 ≤ (8905523454549/20000000000000 : ℝ)^3321
        have hw : |(1347032521/2500000000 : ℝ)|=(1347032521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_2 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285680277/10000000000 : ℝ)*x 0 + (5388130627/10000000000 : ℝ)*x 1 + (-1984046097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285680277/10000000000 : ℝ)^4345 ≤ (10855793869429/25000000000000 : ℝ)^3321 := by
    have hnat : (5285680277 : ℕ)^4345*25000000000000^3321 ≤ 10855793869429^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285680277 10000000000 10855793869429 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388130627/10000000000 : ℝ)^4345 ≤ (22263811571873/50000000000000 : ℝ)^3321 := by
    have hnat : (5388130627 : ℕ)^4345*50000000000000^3321 ≤ 22263811571873^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388130627 10000000000 22263811571873 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984046097/10000000000 : ℝ)^4345 ≤ (12049201368913/100000000000000 : ℝ)^3321 := by
    have hnat : (1984046097 : ℕ)^4345*100000000000000^3321 ≤ 12049201368913^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984046097 10000000000 12049201368913 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285680277/10000000000 : ℝ), (5388130627/10000000000 : ℝ), (-1984046097/10000000000 : ℝ)] ![(10855793869429/25000000000000 : ℝ), (22263811571873/50000000000000 : ℝ), (12049201368913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285680277/10000000000 : ℝ)|^4345 ≤ (10855793869429/25000000000000 : ℝ)^3321
        have hw : |(5285680277/10000000000 : ℝ)|=(5285680277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388130627/10000000000 : ℝ)|^4345 ≤ (22263811571873/50000000000000 : ℝ)^3321
        have hw : |(5388130627/10000000000 : ℝ)|=(5388130627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984046097/10000000000 : ℝ)|^4345 ≤ (12049201368913/100000000000000 : ℝ)^3321
        have hw : |(-1984046097/10000000000 : ℝ)|=(1984046097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_3 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4462717147/10000000000 : ℝ)*x 0 + (849138199/2000000000 : ℝ)*x 1 + (4245691861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462717147/10000000000 : ℝ)^4345 ≤ (1391927189341/4000000000000 : ℝ)^3321 := by
    have hnat : (4462717147 : ℕ)^4345*4000000000000^3321 ≤ 1391927189341^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462717147 10000000000 1391927189341 4000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849138199/2000000000 : ℝ)^4345 ≤ (32600905775179/100000000000000 : ℝ)^3321 := by
    have hnat : (849138199 : ℕ)^4345*100000000000000^3321 ≤ 32600905775179^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849138199 2000000000 32600905775179 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245691861/10000000000 : ℝ)^4345 ≤ (8150228618799/25000000000000 : ℝ)^3321 := by
    have hnat : (4245691861 : ℕ)^4345*25000000000000^3321 ≤ 8150228618799^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245691861 10000000000 8150228618799 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462717147/10000000000 : ℝ), (849138199/2000000000 : ℝ), (4245691861/10000000000 : ℝ)] ![(1391927189341/4000000000000 : ℝ), (32600905775179/100000000000000 : ℝ), (8150228618799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462717147/10000000000 : ℝ)|^4345 ≤ (1391927189341/4000000000000 : ℝ)^3321
        have hw : |(4462717147/10000000000 : ℝ)|=(4462717147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849138199/2000000000 : ℝ)|^4345 ≤ (32600905775179/100000000000000 : ℝ)^3321
        have hw : |(849138199/2000000000 : ℝ)|=(849138199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245691861/10000000000 : ℝ)|^4345 ≤ (8150228618799/25000000000000 : ℝ)^3321
        have hw : |(4245691861/10000000000 : ℝ)|=(4245691861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_4 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087030663/5000000000 : ℝ)*x 0 + (1316449489/2500000000 : ℝ)*x 1 + (5265797697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087030663/5000000000 : ℝ)^4345 ≤ (3395201955403/25000000000000 : ℝ)^3321 := by
    have hnat : (1087030663 : ℕ)^4345*25000000000000^3321 ≤ 3395201955403^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087030663 5000000000 3395201955403 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316449489/2500000000 : ℝ)^4345 ≤ (10802399367783/25000000000000 : ℝ)^3321 := by
    have hnat : (1316449489 : ℕ)^4345*25000000000000^3321 ≤ 10802399367783^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316449489 2500000000 10802399367783 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265797697/10000000000 : ℝ)^4345 ≤ (43209594690543/100000000000000 : ℝ)^3321 := by
    have hnat : (5265797697 : ℕ)^4345*100000000000000^3321 ≤ 43209594690543^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265797697 10000000000 43209594690543 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087030663/5000000000 : ℝ), (1316449489/2500000000 : ℝ), (5265797697/10000000000 : ℝ)] ![(3395201955403/25000000000000 : ℝ), (10802399367783/25000000000000 : ℝ), (43209594690543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087030663/5000000000 : ℝ)|^4345 ≤ (3395201955403/25000000000000 : ℝ)^3321
        have hw : |(-1087030663/5000000000 : ℝ)|=(1087030663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316449489/2500000000 : ℝ)|^4345 ≤ (10802399367783/25000000000000 : ℝ)^3321
        have hw : |(1316449489/2500000000 : ℝ)|=(1316449489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265797697/10000000000 : ℝ)|^4345 ≤ (43209594690543/100000000000000 : ℝ)^3321
        have hw : |(5265797697/10000000000 : ℝ)|=(5265797697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_5 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371449857/10000000000 : ℝ)*x 0 + (-2033425687/10000000000 : ℝ)*x 1 + (1053159571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371449857/10000000000 : ℝ)^4345 ≤ (44347354199097/100000000000000 : ℝ)^3321 := by
    have hnat : (5371449857 : ℕ)^4345*100000000000000^3321 ≤ 44347354199097^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371449857 10000000000 44347354199097 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033425687/10000000000 : ℝ)^4345 ≤ (6221524700911/50000000000000 : ℝ)^3321 := by
    have hnat : (2033425687 : ℕ)^4345*50000000000000^3321 ≤ 6221524700911^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033425687 10000000000 6221524700911 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053159571/2000000000 : ℝ)^4345 ≤ (43209596386809/100000000000000 : ℝ)^3321 := by
    have hnat : (1053159571 : ℕ)^4345*100000000000000^3321 ≤ 43209596386809^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053159571 2000000000 43209596386809 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371449857/10000000000 : ℝ), (-2033425687/10000000000 : ℝ), (1053159571/2000000000 : ℝ)] ![(44347354199097/100000000000000 : ℝ), (6221524700911/50000000000000 : ℝ), (43209596386809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371449857/10000000000 : ℝ)|^4345 ≤ (44347354199097/100000000000000 : ℝ)^3321
        have hw : |(5371449857/10000000000 : ℝ)|=(5371449857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033425687/10000000000 : ℝ)|^4345 ≤ (6221524700911/50000000000000 : ℝ)^3321
        have hw : |(-2033425687/10000000000 : ℝ)|=(2033425687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053159571/2000000000 : ℝ)|^4345 ≤ (43209596386809/100000000000000 : ℝ)^3321
        have hw : |(1053159571/2000000000 : ℝ)|=(1053159571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_6 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685725053/5000000000 : ℝ)*x 0 + (5265797901/10000000000 : ℝ)*x 1 + (-2033425289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685725053/5000000000 : ℝ)^4345 ≤ (44347356888751/100000000000000 : ℝ)^3321 := by
    have hnat : (2685725053 : ℕ)^4345*100000000000000^3321 ≤ 44347356888751^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685725053 5000000000 44347356888751 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265797901/10000000000 : ℝ)^4345 ≤ (43209596880659/100000000000000 : ℝ)^3321 := by
    have hnat : (5265797901 : ℕ)^4345*100000000000000^3321 ≤ 43209596880659^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265797901 10000000000 43209596880659 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2033425289/10000000000 : ℝ)^4345 ≤ (2488609243081/20000000000000 : ℝ)^3321 := by
    have hnat : (2033425289 : ℕ)^4345*20000000000000^3321 ≤ 2488609243081^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033425289 10000000000 2488609243081 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685725053/5000000000 : ℝ), (5265797901/10000000000 : ℝ), (-2033425289/10000000000 : ℝ)] ![(44347356888751/100000000000000 : ℝ), (43209596880659/100000000000000 : ℝ), (2488609243081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685725053/5000000000 : ℝ)|^4345 ≤ (44347356888751/100000000000000 : ℝ)^3321
        have hw : |(2685725053/5000000000 : ℝ)|=(2685725053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265797901/10000000000 : ℝ)|^4345 ≤ (43209596880659/100000000000000 : ℝ)^3321
        have hw : |(5265797901/10000000000 : ℝ)|=(5265797901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2033425289/10000000000 : ℝ)|^4345 ≤ (2488609243081/20000000000000 : ℝ)^3321
        have hw : |(-2033425289/10000000000 : ℝ)|=(2033425289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_7 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104182493/250000000 : ℝ)*x 0 + (549168487/1250000000 : ℝ)*x 1 + (4393347983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104182493/250000000 : ℝ)^4345 ≤ (1988476378953/6250000000000 : ℝ)^3321 := by
    have hnat : (104182493 : ℕ)^4345*6250000000000^3321 ≤ 1988476378953^3321*250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104182493 250000000 1988476378953 6250000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549168487/1250000000 : ℝ)^4345 ≤ (6818437703577/20000000000000 : ℝ)^3321 := by
    have hnat : (549168487 : ℕ)^4345*20000000000000^3321 ≤ 6818437703577^3321*1250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549168487 1250000000 6818437703577 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4393347983/10000000000 : ℝ)^4345 ≤ (34092189401167/100000000000000 : ℝ)^3321 := by
    have hnat : (4393347983 : ℕ)^4345*100000000000000^3321 ≤ 34092189401167^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393347983 10000000000 34092189401167 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104182493/250000000 : ℝ), (549168487/1250000000 : ℝ), (4393347983/10000000000 : ℝ)] ![(1988476378953/6250000000000 : ℝ), (6818437703577/20000000000000 : ℝ), (34092189401167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104182493/250000000 : ℝ)|^4345 ≤ (1988476378953/6250000000000 : ℝ)^3321
        have hw : |(104182493/250000000 : ℝ)|=(104182493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549168487/1250000000 : ℝ)|^4345 ≤ (6818437703577/20000000000000 : ℝ)^3321
        have hw : |(549168487/1250000000 : ℝ)|=(549168487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4393347983/10000000000 : ℝ)|^4345 ≤ (34092189401167/100000000000000 : ℝ)^3321
        have hw : |(4393347983/10000000000 : ℝ)|=(4393347983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_8 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-420906673/2000000000 : ℝ)*x 0 + (2590691211/5000000000 : ℝ)*x 1 + (5402129393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420906673/2000000000 : ℝ)^4345 ≤ (3253846829787/25000000000000 : ℝ)^3321 := by
    have hnat : (420906673 : ℕ)^4345*25000000000000^3321 ≤ 3253846829787^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420906673 2000000000 3253846829787 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590691211/5000000000 : ℝ)^4345 ≤ (42305572101899/100000000000000 : ℝ)^3321 := by
    have hnat : (2590691211 : ℕ)^4345*100000000000000^3321 ≤ 42305572101899^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590691211 5000000000 42305572101899 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402129393/10000000000 : ℝ)^4345 ≤ (22339520287247/50000000000000 : ℝ)^3321 := by
    have hnat : (5402129393 : ℕ)^4345*50000000000000^3321 ≤ 22339520287247^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402129393 10000000000 22339520287247 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420906673/2000000000 : ℝ), (2590691211/5000000000 : ℝ), (5402129393/10000000000 : ℝ)] ![(3253846829787/25000000000000 : ℝ), (42305572101899/100000000000000 : ℝ), (22339520287247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420906673/2000000000 : ℝ)|^4345 ≤ (3253846829787/25000000000000 : ℝ)^3321
        have hw : |(-420906673/2000000000 : ℝ)|=(420906673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590691211/5000000000 : ℝ)|^4345 ≤ (42305572101899/100000000000000 : ℝ)^3321
        have hw : |(2590691211/5000000000 : ℝ)|=(2590691211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402129393/10000000000 : ℝ)|^4345 ≤ (22339520287247/50000000000000 : ℝ)^3321
        have hw : |(5402129393/10000000000 : ℝ)|=(5402129393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_9 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275860923/10000000000 : ℝ)*x 0 + (-989133121/5000000000 : ℝ)*x 1 + (2701064603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275860923/10000000000 : ℝ)^4345 ≤ (2165883195739/5000000000000 : ℝ)^3321 := by
    have hnat : (5275860923 : ℕ)^4345*5000000000000^3321 ≤ 2165883195739^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275860923 10000000000 2165883195739 5000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989133121/5000000000 : ℝ)^4345 ≤ (1500412189681/12500000000000 : ℝ)^3321 := by
    have hnat : (989133121 : ℕ)^4345*12500000000000^3321 ≤ 1500412189681^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989133121 5000000000 1500412189681 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701064603/5000000000 : ℝ)^4345 ≤ (22339519275501/50000000000000 : ℝ)^3321 := by
    have hnat : (2701064603 : ℕ)^4345*50000000000000^3321 ≤ 22339519275501^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701064603 5000000000 22339519275501 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275860923/10000000000 : ℝ), (-989133121/5000000000 : ℝ), (2701064603/5000000000 : ℝ)] ![(2165883195739/5000000000000 : ℝ), (1500412189681/12500000000000 : ℝ), (22339519275501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275860923/10000000000 : ℝ)|^4345 ≤ (2165883195739/5000000000000 : ℝ)^3321
        have hw : |(5275860923/10000000000 : ℝ)|=(5275860923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989133121/5000000000 : ℝ)|^4345 ≤ (1500412189681/12500000000000 : ℝ)^3321
        have hw : |(-989133121/5000000000 : ℝ)|=(989133121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701064603/5000000000 : ℝ)|^4345 ≤ (22339519275501/50000000000000 : ℝ)^3321
        have hw : |(2701064603/5000000000 : ℝ)|=(2701064603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_10 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275861703/10000000000 : ℝ)*x 0 + (2701064371/5000000000 : ℝ)*x 1 + (-1978265819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275861703/10000000000 : ℝ)^4345 ≤ (10829418073421/25000000000000 : ℝ)^3321 := by
    have hnat : (5275861703 : ℕ)^4345*25000000000000^3321 ≤ 10829418073421^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275861703 10000000000 10829418073421 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701064371/5000000000 : ℝ)^4345 ≤ (44679033530147/100000000000000 : ℝ)^3321 := by
    have hnat : (2701064371 : ℕ)^4345*100000000000000^3321 ≤ 44679033530147^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701064371 5000000000 44679033530147 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978265819/10000000000 : ℝ)^4345 ≤ (480131766379/4000000000000 : ℝ)^3321 := by
    have hnat : (1978265819 : ℕ)^4345*4000000000000^3321 ≤ 480131766379^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978265819 10000000000 480131766379 4000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275861703/10000000000 : ℝ), (2701064371/5000000000 : ℝ), (-1978265819/10000000000 : ℝ)] ![(10829418073421/25000000000000 : ℝ), (44679033530147/100000000000000 : ℝ), (480131766379/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275861703/10000000000 : ℝ)|^4345 ≤ (10829418073421/25000000000000 : ℝ)^3321
        have hw : |(5275861703/10000000000 : ℝ)|=(5275861703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701064371/5000000000 : ℝ)|^4345 ≤ (44679033530147/100000000000000 : ℝ)^3321
        have hw : |(2701064371/5000000000 : ℝ)|=(2701064371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1978265819/10000000000 : ℝ)|^4345 ≤ (480131766379/4000000000000 : ℝ)^3321
        have hw : |(-1978265819/10000000000 : ℝ)|=(1978265819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_11 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4495965021/10000000000 : ℝ)*x 0 + (264298767/625000000 : ℝ)*x 1 + (4228780181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4495965021/10000000000 : ℝ)^4345 ≤ (35137757805459/100000000000000 : ℝ)^3321 := by
    have hnat : (4495965021 : ℕ)^4345*100000000000000^3321 ≤ 35137757805459^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495965021 10000000000 35137757805459 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264298767/625000000 : ℝ)^4345 ≤ (16215560772051/50000000000000 : ℝ)^3321 := by
    have hnat : (264298767 : ℕ)^4345*50000000000000^3321 ≤ 16215560772051^3321*625000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264298767 625000000 16215560772051 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228780181/10000000000 : ℝ)^4345 ≤ (32431120631021/100000000000000 : ℝ)^3321 := by
    have hnat : (4228780181 : ℕ)^4345*100000000000000^3321 ≤ 32431120631021^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228780181 10000000000 32431120631021 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4495965021/10000000000 : ℝ), (264298767/625000000 : ℝ), (4228780181/10000000000 : ℝ)] ![(35137757805459/100000000000000 : ℝ), (16215560772051/50000000000000 : ℝ), (32431120631021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4495965021/10000000000 : ℝ)|^4345 ≤ (35137757805459/100000000000000 : ℝ)^3321
        have hw : |(4495965021/10000000000 : ℝ)|=(4495965021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264298767/625000000 : ℝ)|^4345 ≤ (16215560772051/50000000000000 : ℝ)^3321
        have hw : |(264298767/625000000 : ℝ)|=(264298767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228780181/10000000000 : ℝ)|^4345 ≤ (32431120631021/100000000000000 : ℝ)^3321
        have hw : |(4228780181/10000000000 : ℝ)|=(4228780181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_12 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-956635167/5000000000 : ℝ)*x 0 + (5470433443/10000000000 : ℝ)*x 1 + (1313674173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956635167/5000000000 : ℝ)^4345 ≤ (459598525193/4000000000000 : ℝ)^3321 := by
    have hnat : (956635167 : ℕ)^4345*4000000000000^3321 ≤ 459598525193^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956635167 5000000000 459598525193 4000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470433443/10000000000 : ℝ)^4345 ≤ (4541958227777/10000000000000 : ℝ)^3321 := by
    have hnat : (5470433443 : ℕ)^4345*10000000000000^3321 ≤ 4541958227777^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470433443 10000000000 4541958227777 10000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313674173/2500000000 : ℝ)^4345 ≤ (43090454584219/100000000000000 : ℝ)^3321 := by
    have hnat : (1313674173 : ℕ)^4345*100000000000000^3321 ≤ 43090454584219^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313674173 2500000000 43090454584219 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956635167/5000000000 : ℝ), (5470433443/10000000000 : ℝ), (1313674173/2500000000 : ℝ)] ![(459598525193/4000000000000 : ℝ), (4541958227777/10000000000000 : ℝ), (43090454584219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956635167/5000000000 : ℝ)|^4345 ≤ (459598525193/4000000000000 : ℝ)^3321
        have hw : |(-956635167/5000000000 : ℝ)|=(956635167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470433443/10000000000 : ℝ)|^4345 ≤ (4541958227777/10000000000000 : ℝ)^3321
        have hw : |(5470433443/10000000000 : ℝ)|=(5470433443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313674173/2500000000 : ℝ)|^4345 ≤ (43090454584219/100000000000000 : ℝ)^3321
        have hw : |(1313674173/2500000000 : ℝ)|=(1313674173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_13 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689614933/5000000000 : ℝ)*x 0 + (-2037805441/10000000000 : ℝ)*x 1 + (5254697483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689614933/5000000000 : ℝ)^4345 ≤ (44431411245987/100000000000000 : ℝ)^3321 := by
    have hnat : (2689614933 : ℕ)^4345*100000000000000^3321 ≤ 44431411245987^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689614933 5000000000 44431411245987 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2037805441/10000000000 : ℝ)^4345 ≤ (779882853767/6250000000000 : ℝ)^3321 := by
    have hnat : (2037805441 : ℕ)^4345*6250000000000^3321 ≤ 779882853767^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037805441 10000000000 779882853767 6250000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254697483/10000000000 : ℝ)^4345 ≤ (21545231535381/50000000000000 : ℝ)^3321 := by
    have hnat : (5254697483 : ℕ)^4345*50000000000000^3321 ≤ 21545231535381^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254697483 10000000000 21545231535381 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689614933/5000000000 : ℝ), (-2037805441/10000000000 : ℝ), (5254697483/10000000000 : ℝ)] ![(44431411245987/100000000000000 : ℝ), (779882853767/6250000000000 : ℝ), (21545231535381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689614933/5000000000 : ℝ)|^4345 ≤ (44431411245987/100000000000000 : ℝ)^3321
        have hw : |(2689614933/5000000000 : ℝ)|=(2689614933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2037805441/10000000000 : ℝ)|^4345 ≤ (779882853767/6250000000000 : ℝ)^3321
        have hw : |(-2037805441/10000000000 : ℝ)|=(2037805441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254697483/10000000000 : ℝ)|^4345 ≤ (21545231535381/50000000000000 : ℝ)^3321
        have hw : |(5254697483/10000000000 : ℝ)|=(5254697483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_14 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689614891/5000000000 : ℝ)*x 0 + (5254697993/10000000000 : ℝ)*x 1 + (-254725609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689614891/5000000000 : ℝ)^4345 ≤ (44431410338229/100000000000000 : ℝ)^3321 := by
    have hnat : (2689614891 : ℕ)^4345*100000000000000^3321 ≤ 44431410338229^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689614891 5000000000 44431410338229 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254697993/10000000000 : ℝ)^4345 ≤ (43090468542491/100000000000000 : ℝ)^3321 := by
    have hnat : (5254697993 : ℕ)^4345*100000000000000^3321 ≤ 43090468542491^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254697993 10000000000 43090468542491 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254725609/1250000000 : ℝ)^4345 ≤ (2495624220359/20000000000000 : ℝ)^3321 := by
    have hnat : (254725609 : ℕ)^4345*20000000000000^3321 ≤ 2495624220359^3321*1250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254725609 1250000000 2495624220359 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689614891/5000000000 : ℝ), (5254697993/10000000000 : ℝ), (-254725609/1250000000 : ℝ)] ![(44431410338229/100000000000000 : ℝ), (43090468542491/100000000000000 : ℝ), (2495624220359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689614891/5000000000 : ℝ)|^4345 ≤ (44431410338229/100000000000000 : ℝ)^3321
        have hw : |(2689614891/5000000000 : ℝ)|=(2689614891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254697993/10000000000 : ℝ)|^4345 ≤ (43090468542491/100000000000000 : ℝ)^3321
        have hw : |(5254697993/10000000000 : ℝ)|=(5254697993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254725609/1250000000 : ℝ)|^4345 ≤ (2495624220359/20000000000000 : ℝ)^3321
        have hw : |(-254725609/1250000000 : ℝ)|=(254725609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_box_15 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2070021689/5000000000 : ℝ)*x 0 + (2203367791/5000000000 : ℝ)*x 1 + (4406736643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070021689/5000000000 : ℝ)^4345 ≤ (31543643077427/100000000000000 : ℝ)^3321 := by
    have hnat : (2070021689 : ℕ)^4345*100000000000000^3321 ≤ 31543643077427^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070021689 5000000000 31543643077427 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203367791/5000000000 : ℝ)^4345 ≤ (34228173061691/100000000000000 : ℝ)^3321 := by
    have hnat : (2203367791 : ℕ)^4345*100000000000000^3321 ≤ 34228173061691^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203367791 5000000000 34228173061691 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406736643/10000000000 : ℝ)^4345 ≤ (34228183843783/100000000000000 : ℝ)^3321 := by
    have hnat : (4406736643 : ℕ)^4345*100000000000000^3321 ≤ 34228183843783^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406736643 10000000000 34228183843783 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070021689/5000000000 : ℝ), (2203367791/5000000000 : ℝ), (4406736643/10000000000 : ℝ)] ![(31543643077427/100000000000000 : ℝ), (34228173061691/100000000000000 : ℝ), (34228183843783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070021689/5000000000 : ℝ)|^4345 ≤ (31543643077427/100000000000000 : ℝ)^3321
        have hw : |(2070021689/5000000000 : ℝ)|=(2070021689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2203367791/5000000000 : ℝ)|^4345 ≤ (34228173061691/100000000000000 : ℝ)^3321
        have hw : |(2203367791/5000000000 : ℝ)|=(2203367791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4406736643/10000000000 : ℝ)|^4345 ≤ (34228183843783/100000000000000 : ℝ)^3321
        have hw : |(4406736643/10000000000 : ℝ)|=(4406736643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1385_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(503/800 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2361/4000 : ℝ) ∧ (40101/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42259/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11247/100000 : ℝ) ^ (543/128 : ℝ) ≤ (1178229095669727/12500000000000000000 : ℝ) := by
    have hpowers : (11247/100000 : ℝ)^543 ≤ (1178229095669727/12500000000000000000 : ℝ)^128 := by
      have hnat : (11247 : ℕ)^543*12500000000000000000^128 ≤ 1178229095669727^128*100000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11247 100000 1178229095669727 12500000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11247/100000 : ℝ)) (X := (1178229095669727/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3683/25000 : ℝ) ^ (543/128 : ℝ) ≤ (29621716673060979/100000000000000000000 : ℝ) := by
    have hpowers : (3683/25000 : ℝ)^543 ≤ (29621716673060979/100000000000000000000 : ℝ)^128 := by
      have hnat : (3683 : ℕ)^543*100000000000000000000^128 ≤ 29621716673060979^128*25000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3683 25000 29621716673060979 100000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3683/25000 : ℝ)) (X := (29621716673060979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251178229095669727/6250000000000000000 : ℝ) ≤ (5000222176738123/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (6251178229095669727/6250000000000000000 : ℝ)^128 ≤ (5000222176738123/5000000000000000 : ℝ)^543 := by
      have hnat : (6251178229095669727 : ℕ)^128*5000000000000000^543 ≤ 5000222176738123^543*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251178229095669727 6250000000000000000 5000222176738123 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000222176738123/5000000000000000 : ℝ)) (X := (6251178229095669727/6250000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007809509887683759/20000000000000000000 : ℝ) ≤ (5000460160286429/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (20007809509887683759/20000000000000000000 : ℝ)^128 ≤ (5000460160286429/5000000000000000 : ℝ)^543 := by
      have hnat : (20007809509887683759 : ℕ)^128*5000000000000000^543 ≤ 5000460160286429^543*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007809509887683759 20000000000000000000 5000460160286429 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000460160286429/5000000000000000 : ℝ)) (X := (20007809509887683759/20000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029621716673060979/50000000000000000000 : ℝ) ≤ (1000139628766947/1000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (50029621716673060979/50000000000000000000 : ℝ)^128 ≤ (1000139628766947/1000000000000000 : ℝ)^543 := by
      have hnat : (50029621716673060979 : ℕ)^128*1000000000000000^543 ≤ 1000139628766947^543*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029621716673060979 50000000000000000000 1000139628766947 1000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000139628766947/1000000000000000 : ℝ)) (X := (50029621716673060979/50000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1178229095669727/12500000000000000000 : ℝ) ≤ ((17420421083996763491/17425000000000000000 : ℝ)+2*(118991774153/87125000000000 : ℝ)*(11247/100000 : ℝ))^(543/128 : ℝ) := by
    rw [show (17420421083996763491/17425000000000000000 : ℝ)+2*(118991774153/87125000000000 : ℝ)*(11247/100000 : ℝ)=(5000222176738123/5000000000000000 : ℝ) by norm_num, show 1+2*(1178229095669727/12500000000000000000 : ℝ)=(6251178229095669727/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29621716673060979/100000000000000000000 : ℝ)+(1178229095669727/12500000000000000000 : ℝ) ≤ ((17420421083996763491/17425000000000000000 : ℝ)+(118991774153/87125000000000 : ℝ)*((3683/25000 : ℝ)+(11247/100000 : ℝ)))^(543/128 : ℝ) := by
    rw [show (17420421083996763491/17425000000000000000 : ℝ)+(118991774153/87125000000000 : ℝ)*((3683/25000 : ℝ)+(11247/100000 : ℝ))=(5000460160286429/5000000000000000 : ℝ) by norm_num, show 1+(29621716673060979/100000000000000000000 : ℝ)+(1178229095669727/12500000000000000000 : ℝ)=(20007809509887683759/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29621716673060979/100000000000000000000 : ℝ) ≤ ((17420421083996763491/17425000000000000000 : ℝ)+2*(118991774153/87125000000000 : ℝ)*(3683/25000 : ℝ))^(543/128 : ℝ) := by
    rw [show (17420421083996763491/17425000000000000000 : ℝ)+2*(118991774153/87125000000000 : ℝ)*(3683/25000 : ℝ)=(1000139628766947/1000000000000000 : ℝ) by norm_num, show 1+2*(29621716673060979/100000000000000000000 : ℝ)=(50029621716673060979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17420421083996763491/17425000000000000000 : ℝ)*(X 1 0+X 2 0)+(118991774153/87125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (17420421083996763491/17425000000000000000 : ℝ)) (alpha := (118991774153/87125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17420421083996763491/17425000000000000000 : ℝ)*(X 0 1+X 2 1)+(118991774153/87125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (17420421083996763491/17425000000000000000 : ℝ)) (alpha := (118991774153/87125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17420421083996763491/17425000000000000000 : ℝ)*(X 0 2+X 1 2)+(118991774153/87125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (17420421083996763491/17425000000000000000 : ℝ)) (alpha := (118991774153/87125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-230435827/1250000000 : ℝ)*X 0 0+(2694064839/5000000000 : ℝ)*X 0 1+(1347032429/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285681069/10000000000 : ℝ)*X 1 0+(-1984045763/10000000000 : ℝ)*X 1 1+(1347032521/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285680277/10000000000 : ℝ)*X 2 0+(5388130627/10000000000 : ℝ)*X 2 1+(-1984046097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4462717147/10000000000 : ℝ)*X 0 0+(849138199/2000000000 : ℝ)*X 0 1+(4245691861/10000000000 : ℝ)*X 0 2+(4462717147/10000000000 : ℝ)*X 1 0+(849138199/2000000000 : ℝ)*X 1 1+(4245691861/10000000000 : ℝ)*X 1 2+(4462717147/10000000000 : ℝ)*X 2 0+(849138199/2000000000 : ℝ)*X 2 1+(4245691861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087030663/5000000000 : ℝ)*X 0 0+(1316449489/2500000000 : ℝ)*X 0 1+(5265797697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371449857/10000000000 : ℝ)*X 1 0+(-2033425687/10000000000 : ℝ)*X 1 1+(1053159571/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685725053/5000000000 : ℝ)*X 2 0+(5265797901/10000000000 : ℝ)*X 2 1+(-2033425289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((104182493/250000000 : ℝ)*X 0 0+(549168487/1250000000 : ℝ)*X 0 1+(4393347983/10000000000 : ℝ)*X 0 2+(104182493/250000000 : ℝ)*X 1 0+(549168487/1250000000 : ℝ)*X 1 1+(4393347983/10000000000 : ℝ)*X 1 2+(104182493/250000000 : ℝ)*X 2 0+(549168487/1250000000 : ℝ)*X 2 1+(4393347983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-420906673/2000000000 : ℝ)*X 0 0+(2590691211/5000000000 : ℝ)*X 0 1+(5402129393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275860923/10000000000 : ℝ)*X 1 0+(-989133121/5000000000 : ℝ)*X 1 1+(2701064603/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275861703/10000000000 : ℝ)*X 2 0+(2701064371/5000000000 : ℝ)*X 2 1+(-1978265819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4495965021/10000000000 : ℝ)*X 0 0+(264298767/625000000 : ℝ)*X 0 1+(4228780181/10000000000 : ℝ)*X 0 2+(4495965021/10000000000 : ℝ)*X 1 0+(264298767/625000000 : ℝ)*X 1 1+(4228780181/10000000000 : ℝ)*X 1 2+(4495965021/10000000000 : ℝ)*X 2 0+(264298767/625000000 : ℝ)*X 2 1+(4228780181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-956635167/5000000000 : ℝ)*X 0 0+(5470433443/10000000000 : ℝ)*X 0 1+(1313674173/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2689614933/5000000000 : ℝ)*X 1 0+(-2037805441/10000000000 : ℝ)*X 1 1+(5254697483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689614891/5000000000 : ℝ)*X 2 0+(5254697993/10000000000 : ℝ)*X 2 1+(-254725609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2070021689/5000000000 : ℝ)*X 0 0+(2203367791/5000000000 : ℝ)*X 0 1+(4406736643/10000000000 : ℝ)*X 0 2+(2070021689/5000000000 : ℝ)*X 1 0+(2203367791/5000000000 : ℝ)*X 1 1+(4406736643/10000000000 : ℝ)*X 1 2+(2070021689/5000000000 : ℝ)*X 2 0+(2203367791/5000000000 : ℝ)*X 2 1+(4406736643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-503/800 : ℝ) ≤ (-68471739188958498266763457577607/108906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50869743/50000000000000 : ℝ)*(upper0) + (38328209/20000000000000 : ℝ)*(lower2) + (25205503/100000000000000 : ℝ)*(upper5) + (371065805516597/12500000000000 : ℝ)*(major0) + (371065805516597/12500000000000 : ℝ)*(major1) + (371065805516597/12500000000000 : ℝ)*(major2) + (889754143/50000000000000 : ℝ)*(sp1) + (18414411/800000000000 : ℝ)*(sp3) + (50753473477673/1250000000000 : ℝ)*(sp4) + (4060282401099933/100000000000000 : ℝ)*(sp5) + (1015046854767383/25000000000000 : ℝ)*(sp6) + (948861900460477/50000000000000 : ℝ)*(sp7) + (315119719/5000000000000 : ℝ)*(sp8) + (96761538687/100000000000000 : ℝ)*(sp14) + (1897726102722329/100000000000000 : ℝ)*(f.failure) + (4060284180608219/100000000000000 : ℝ)*(f.sum) + (15970974827287/17425000000000000000000000000 : ℝ)*base65 + (3417636520676702373/217812500000000000000000000000000 : ℝ)*base68 + (4002256633519202373/217812500000000000000000000000000 : ℝ)*base70 + (3586196607135139873/217812500000000000000000000000000 : ℝ)*base72 + (7637954641739/2178125000000000000000000000 : ℝ)*base73 + (3073151695251389873/217812500000000000000000000000000 : ℝ)*base76 + (3617550566437327373/217812500000000000000000000000000 : ℝ)*base78 + (4398426196217639873/217812500000000000000000000000000 : ℝ)*base80 + (10595134519213/17425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (58547209/5000000000000000000000 : ℝ)*base89 + (58547209/5000000000000000000000 : ℝ)*base91 + (58547209/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2361/4000 : ℝ) ≤ (514281217595937147276087177535929/871250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8571549/50000000000000 : ℝ)*(lower1) + (131480297/100000000000000 : ℝ)*(upper2) + (10671249/6250000000000 : ℝ)*(lower4) + (3038667704061873/100000000000000 : ℝ)*(major0) + (3038667704061873/100000000000000 : ℝ)*(major1) + (3038667704061873/100000000000000 : ℝ)*(major2) + (411508294511601/10000000000000 : ℝ)*(sp0) + (4115071031833211/100000000000000 : ℝ)*(sp1) + (4115068269464259/100000000000000 : ℝ)*(sp2) + (1942562455099079/100000000000000 : ℝ)*(sp3) + (2222381441/10000000000000 : ℝ)*(sp5) + (12493091681/50000000000000 : ℝ)*(sp6) + (3706268631/100000000000000 : ℝ)*(sp7) + (10310531611/100000000000000 : ℝ)*(sp12) + (194256616136771/10000000000000 : ℝ)*(f.failure) + (2057546627823811/50000000000000 : ℝ)*(f.sum) + (214185412505799/17425000000000000000000000000 : ℝ)*base66 + (220094616380278643/1742500000000000000000000000000000 : ℝ)*base67 + (5322529242394721357/1742500000000000000000000000000000 : ℝ)*base70 + (23707492701909721357/1742500000000000000000000000000000 : ℝ)*base72 + (12869794720937/8712500000000000000000000000 : ℝ)*base74 + (1082854926370278643/1742500000000000000000000000000000 : ℝ)*base75 + (22253958771014721357/1742500000000000000000000000000000 : ℝ)*base78 + (9997005521354721357/1742500000000000000000000000000000 : ℝ)*base80 + (63227198326899/17425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3063891/500000000000000000000 : ℝ)*base89 + (3063891/500000000000000000000 : ℝ)*base91 + (3063891/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40101/50000 : ℝ) ≤ (642265131219491724054684859671/800781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (498083/2500000000000 : ℝ)*(upper0) + (24587659/12500000000000 : ℝ)*(lower3) + (69436269/25000000000000 : ℝ)*(upper4) + (104651416469441/3125000000000 : ℝ)*(major0) + (104651416469441/3125000000000 : ℝ)*(major1) + (104651416469441/3125000000000 : ℝ)*(major2) + (802609601/400000000000 : ℝ)*(sp1) + (123684944659/100000000000000 : ℝ)*(sp2) + (47459429579/50000000000000 : ℝ)*(sp3) + (6194719167/50000000000000 : ℝ)*(sp4) + (1132521533157361/25000000000000 : ℝ)*(sp8) + (4529897869667527/100000000000000 : ℝ)*(sp9) + (2264987418561559/50000000000000 : ℝ)*(sp10) + (2140762274321803/100000000000000 : ℝ)*(sp11) + (2140857193180961/100000000000000 : ℝ)*(f.failure) + (4530098522067777/100000000000000 : ℝ)*(f.sum) + (5736625978407/1025000000000000000000000000 : ℝ)*base65 + (24077799502842807/3203125000000000000000000000000 : ℝ)*base68 + (226620307961973/200195312500000000000000000000 : ℝ)*base69 + (19744735111063443/3203125000000000000000000000000 : ℝ)*base71 + (8047846399259/512500000000000000000000000 : ℝ)*base74 + (58406142180723/200195312500000000000000000000 : ℝ)*base75 + (9085613324657193/3203125000000000000000000000000 : ℝ)*base77 + (11663810675845821/400390625000000000000000000000 : ℝ)*base79 + (37389898829/128125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5204881/5000000000000000000000 : ℝ)*base89 + (5204881/5000000000000000000000 : ℝ)*base91 + (5204881/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42259/50000 : ℝ) ≤ (-73634243610463337127269206208781/87125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2424219/10000000000000 : ℝ)*(lower0) + (11472697/4000000000000 : ℝ)*(upper3) + (782519923/100000000000000 : ℝ)*(upper5) + (338580671905799/10000000000000 : ℝ)*(major0) + (338580671905799/10000000000000 : ℝ)*(major1) + (338580671905799/10000000000000 : ℝ)*(major2) + (10409000677/50000000000000 : ℝ)*(sp4) + (6255859533/12500000000000 : ℝ)*(sp5) + (3350353387/1562500000000 : ℝ)*(sp7) + (1523116299/20000000000000 : ℝ)*(sp8) + (579408866067523/12500000000000 : ℝ)*(sp12) + (463524931524677/10000000000000 : ℝ)*(sp13) + (2317649681061517/50000000000000 : ℝ)*(sp14) + (1082135765207543/50000000000000 : ℝ)*(sp15) + (1082242976515927/50000000000000 : ℝ)*(f.failure) + (2317649681061517/50000000000000 : ℝ)*(f.sum) + (12962004340529/3485000000000000000000000000 : ℝ)*base66 + (944268941188284309/174250000000000000000000000000000 : ℝ)*base67 + (2411817455091034309/174250000000000000000000000000000 : ℝ)*base69 + (1552395250085784309/174250000000000000000000000000000 : ℝ)*base71 + (7887118311197/1742500000000000000000000000 : ℝ)*base74 + (1009425918537784309/174250000000000000000000000000000 : ℝ)*base75 + (1319340837725784309/174250000000000000000000000000000 : ℝ)*base77 + (620863740340284309/174250000000000000000000000000000 : ℝ)*base79 + (6286305084557/1742500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (507367/2500000000000000000000 : ℝ)*base89 + (507367/2500000000000000000000 : ℝ)*base91 + (507367/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1385_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(503/800 : ℝ) ≤ X j i ∧ X j i ≤ -(2361/4000 : ℝ) else (40101/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42259/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1385_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1385_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(503/800 : ℝ) ≤ X j i ∧ X j i ≤ -(2361/4000 : ℝ) else (40101/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42259/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1385_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1385_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1385_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(503/800 : ℝ) ≤ X j i ∧ X j i ≤ -(2361/4000 : ℝ) else (40101/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42259/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1385_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
