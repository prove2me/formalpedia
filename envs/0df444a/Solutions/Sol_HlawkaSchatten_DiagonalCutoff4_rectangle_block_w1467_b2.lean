-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1467_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:29.710302+00:00
-- url     : https://prove2.me/submissions/834e66fe-2589-4401-8b9b-c835e9727bed

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
theorem support_rectangle_w1467_s6_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936602207/10000000000 : ℝ)*x 0 + (217566091/400000000 : ℝ)*x 1 + (1043003993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936602207/10000000000 : ℝ)^4431 ≤ (11823742124043/100000000000000 : ℝ)^3407 := by
    have hnat : (1936602207 : ℕ)^4431*100000000000000^3407 ≤ 11823742124043^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936602207 10000000000 11823742124043 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217566091/400000000 : ℝ)^4431 ≤ (45294252318563/100000000000000 : ℝ)^3407 := by
    have hnat : (217566091 : ℕ)^4431*100000000000000^3407 ≤ 45294252318563^3407*400000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217566091 400000000 45294252318563 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043003993/2000000000 : ℝ)^4431 ≤ (21441002772607/50000000000000 : ℝ)^3407 := by
    have hnat : (1043003993 : ℕ)^4431*50000000000000^3407 ≤ 21441002772607^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043003993 2000000000 21441002772607 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936602207/10000000000 : ℝ), (217566091/400000000 : ℝ), (1043003993/2000000000 : ℝ)] ![(11823742124043/100000000000000 : ℝ), (45294252318563/100000000000000 : ℝ), (21441002772607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936602207/10000000000 : ℝ)|^4431 ≤ (11823742124043/100000000000000 : ℝ)^3407
        have hw : |(-1936602207/10000000000 : ℝ)|=(1936602207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217566091/400000000 : ℝ)|^4431 ≤ (45294252318563/100000000000000 : ℝ)^3407
        have hw : |(217566091/400000000 : ℝ)|=(217566091/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043003993/2000000000 : ℝ)|^4431 ≤ (21441002772607/50000000000000 : ℝ)^3407
        have hw : |(1043003993/2000000000 : ℝ)|=(1043003993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s6_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214158781/400000000 : ℝ)*x 0 + (-102575089/500000000 : ℝ)*x 1 + (5215020011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214158781/400000000 : ℝ)^4431 ≤ (8874774936149/20000000000000 : ℝ)^3407 := by
    have hnat : (214158781 : ℕ)^4431*20000000000000^3407 ≤ 8874774936149^3407*400000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214158781 400000000 8874774936149 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102575089/500000000 : ℝ)^4431 ≤ (2548823852227/20000000000000 : ℝ)^3407 := by
    have hnat : (102575089 : ℕ)^4431*20000000000000^3407 ≤ 2548823852227^3407*500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102575089 500000000 2548823852227 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215020011/10000000000 : ℝ)^4431 ≤ (10720501509287/25000000000000 : ℝ)^3407 := by
    have hnat : (5215020011 : ℕ)^4431*25000000000000^3407 ≤ 10720501509287^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215020011 10000000000 10720501509287 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214158781/400000000 : ℝ), (-102575089/500000000 : ℝ), (5215020011/10000000000 : ℝ)] ![(8874774936149/20000000000000 : ℝ), (2548823852227/20000000000000 : ℝ), (10720501509287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214158781/400000000 : ℝ)|^4431 ≤ (8874774936149/20000000000000 : ℝ)^3407
        have hw : |(214158781/400000000 : ℝ)|=(214158781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102575089/500000000 : ℝ)|^4431 ≤ (2548823852227/20000000000000 : ℝ)^3407
        have hw : |(-102575089/500000000 : ℝ)|=(102575089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215020011/10000000000 : ℝ)|^4431 ≤ (10720501509287/25000000000000 : ℝ)^3407
        have hw : |(5215020011/10000000000 : ℝ)|=(5215020011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s6_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669246181/1250000000 : ℝ)*x 0 + (5215019957/10000000000 : ℝ)*x 1 + (-410300391/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669246181/1250000000 : ℝ)^4431 ≤ (44373873850757/100000000000000 : ℝ)^3407 := by
    have hnat : (669246181 : ℕ)^4431*100000000000000^3407 ≤ 44373873850757^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669246181 1250000000 44373873850757 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215019957/10000000000 : ℝ)^4431 ≤ (2144100272983/5000000000000 : ℝ)^3407 := by
    have hnat : (5215019957 : ℕ)^4431*5000000000000^3407 ≤ 2144100272983^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215019957 10000000000 2144100272983 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410300391/2000000000 : ℝ)^4431 ≤ (796507542187/6250000000000 : ℝ)^3407 := by
    have hnat : (410300391 : ℕ)^4431*6250000000000^3407 ≤ 796507542187^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410300391 2000000000 796507542187 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669246181/1250000000 : ℝ), (5215019957/10000000000 : ℝ), (-410300391/2000000000 : ℝ)] ![(44373873850757/100000000000000 : ℝ), (2144100272983/5000000000000 : ℝ), (796507542187/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669246181/1250000000 : ℝ)|^4431 ≤ (44373873850757/100000000000000 : ℝ)^3407
        have hw : |(669246181/1250000000 : ℝ)|=(669246181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215019957/10000000000 : ℝ)|^4431 ≤ (2144100272983/5000000000000 : ℝ)^3407
        have hw : |(5215019957/10000000000 : ℝ)|=(5215019957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410300391/2000000000 : ℝ)|^4431 ≤ (796507542187/6250000000000 : ℝ)^3407
        have hw : |(-410300391/2000000000 : ℝ)|=(410300391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s6_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291198637/10000000000 : ℝ)*x 0 + (4051337687/10000000000 : ℝ)*x 1 + (4543503603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291198637/10000000000 : ℝ)^4431 ≤ (6655448044829/20000000000000 : ℝ)^3407 := by
    have hnat : (4291198637 : ℕ)^4431*20000000000000^3407 ≤ 6655448044829^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291198637 10000000000 6655448044829 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051337687/10000000000 : ℝ)^4431 ≤ (15439354847413/50000000000000 : ℝ)^3407 := by
    have hnat : (4051337687 : ℕ)^4431*50000000000000^3407 ≤ 15439354847413^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051337687 10000000000 15439354847413 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4543503603/10000000000 : ℝ)^4431 ≤ (17922025028283/50000000000000 : ℝ)^3407 := by
    have hnat : (4543503603 : ℕ)^4431*50000000000000^3407 ≤ 17922025028283^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543503603 10000000000 17922025028283 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291198637/10000000000 : ℝ), (4051337687/10000000000 : ℝ), (4543503603/10000000000 : ℝ)] ![(6655448044829/20000000000000 : ℝ), (15439354847413/50000000000000 : ℝ), (17922025028283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291198637/10000000000 : ℝ)|^4431 ≤ (6655448044829/20000000000000 : ℝ)^3407
        have hw : |(4291198637/10000000000 : ℝ)|=(4291198637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4051337687/10000000000 : ℝ)|^4431 ≤ (15439354847413/50000000000000 : ℝ)^3407
        have hw : |(4051337687/10000000000 : ℝ)|=(4051337687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4543503603/10000000000 : ℝ)|^4431 ≤ (17922025028283/50000000000000 : ℝ)^3407
        have hw : |(4543503603/10000000000 : ℝ)|=(4543503603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s6_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38732663/200000000 : ℝ)*x 0 + (2608081877/5000000000 : ℝ)*x 1 + (54380001/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38732663/200000000 : ℝ)^4431 ≤ (11823987825427/100000000000000 : ℝ)^3407 := by
    have hnat : (38732663 : ℕ)^4431*100000000000000^3407 ≤ 11823987825427^3407*200000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38732663 200000000 11823987825427 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608081877/5000000000 : ℝ)^4431 ≤ (42894237868731/100000000000000 : ℝ)^3407 := by
    have hnat : (2608081877 : ℕ)^4431*100000000000000^3407 ≤ 42894237868731^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608081877 5000000000 42894237868731 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54380001/100000000 : ℝ)^4431 ≤ (11320443571493/25000000000000 : ℝ)^3407 := by
    have hnat : (54380001 : ℕ)^4431*25000000000000^3407 ≤ 11320443571493^3407*100000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54380001 100000000 11320443571493 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38732663/200000000 : ℝ), (2608081877/5000000000 : ℝ), (54380001/100000000 : ℝ)] ![(11823987825427/100000000000000 : ℝ), (42894237868731/100000000000000 : ℝ), (11320443571493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38732663/200000000 : ℝ)|^4431 ≤ (11823987825427/100000000000000 : ℝ)^3407
        have hw : |(-38732663/200000000 : ℝ)|=(38732663/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608081877/5000000000 : ℝ)|^4431 ≤ (42894237868731/100000000000000 : ℝ)^3407
        have hw : |(2608081877/5000000000 : ℝ)|=(2608081877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54380001/100000000 : ℝ)|^4431 ≤ (11320443571493/25000000000000 : ℝ)^3407
        have hw : |(54380001/100000000 : ℝ)|=(54380001/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s6_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295567763/10000000000 : ℝ)*x 0 + (-1828521489/10000000000 : ℝ)*x 1 + (5438000523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295567763/10000000000 : ℝ)^4431 ≤ (8749078578793/20000000000000 : ℝ)^3407 := by
    have hnat : (5295567763 : ℕ)^4431*20000000000000^3407 ≤ 8749078578793^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295567763 10000000000 8749078578793 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1828521489/10000000000 : ℝ)^4431 ≤ (1371603528071/12500000000000 : ℝ)^3407 := by
    have hnat : (1828521489 : ℕ)^4431*12500000000000^3407 ≤ 1371603528071^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828521489 10000000000 1371603528071 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438000523/10000000000 : ℝ)^4431 ≤ (11320444716727/25000000000000 : ℝ)^3407 := by
    have hnat : (5438000523 : ℕ)^4431*25000000000000^3407 ≤ 11320444716727^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438000523 10000000000 11320444716727 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295567763/10000000000 : ℝ), (-1828521489/10000000000 : ℝ), (5438000523/10000000000 : ℝ)] ![(8749078578793/20000000000000 : ℝ), (1371603528071/12500000000000 : ℝ), (11320444716727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295567763/10000000000 : ℝ)|^4431 ≤ (8749078578793/20000000000000 : ℝ)^3407
        have hw : |(5295567763/10000000000 : ℝ)|=(5295567763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1828521489/10000000000 : ℝ)|^4431 ≤ (1371603528071/12500000000000 : ℝ)^3407
        have hw : |(-1828521489/10000000000 : ℝ)|=(1828521489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438000523/10000000000 : ℝ)|^4431 ≤ (11320444716727/25000000000000 : ℝ)^3407
        have hw : |(5438000523/10000000000 : ℝ)|=(5438000523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s6_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647784021/5000000000 : ℝ)*x 0 + (5438000059/10000000000 : ℝ)*x 1 + (-1828521749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647784021/5000000000 : ℝ)^4431 ≤ (43745395891427/100000000000000 : ℝ)^3407 := by
    have hnat : (2647784021 : ℕ)^4431*100000000000000^3407 ≤ 43745395891427^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647784021 5000000000 43745395891427 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438000059/10000000000 : ℝ)^4431 ≤ (45281773841957/100000000000000 : ℝ)^3407 := by
    have hnat : (5438000059 : ℕ)^4431*100000000000000^3407 ≤ 45281773841957^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438000059 10000000000 45281773841957 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1828521749/10000000000 : ℝ)^4431 ≤ (1371603781719/12500000000000 : ℝ)^3407 := by
    have hnat : (1828521749 : ℕ)^4431*12500000000000^3407 ≤ 1371603781719^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828521749 10000000000 1371603781719 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647784021/5000000000 : ℝ), (5438000059/10000000000 : ℝ), (-1828521749/10000000000 : ℝ)] ![(43745395891427/100000000000000 : ℝ), (45281773841957/100000000000000 : ℝ), (1371603781719/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647784021/5000000000 : ℝ)|^4431 ≤ (43745395891427/100000000000000 : ℝ)^3407
        have hw : |(2647784021/5000000000 : ℝ)|=(2647784021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438000059/10000000000 : ℝ)|^4431 ≤ (45281773841957/100000000000000 : ℝ)^3407
        have hw : |(5438000059/10000000000 : ℝ)|=(5438000059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1828521749/10000000000 : ℝ)|^4431 ≤ (1371603781719/12500000000000 : ℝ)^3407
        have hw : |(-1828521749/10000000000 : ℝ)|=(1828521749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s6_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21456331/50000000 : ℝ)*x 0 + (908198379/2000000000 : ℝ)*x 1 + (4053868261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21456331/50000000 : ℝ)^4431 ≤ (33277921633753/100000000000000 : ℝ)^3407 := by
    have hnat : (21456331 : ℕ)^4431*100000000000000^3407 ≤ 33277921633753^3407*50000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21456331 50000000 33277921633753 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908198379/2000000000 : ℝ)^4431 ≤ (7163656314407/20000000000000 : ℝ)^3407 := by
    have hnat : (908198379 : ℕ)^4431*20000000000000^3407 ≤ 7163656314407^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908198379 2000000000 7163656314407 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4053868261/10000000000 : ℝ)^4431 ≤ (3862974596871/12500000000000 : ℝ)^3407 := by
    have hnat : (4053868261 : ℕ)^4431*12500000000000^3407 ≤ 3862974596871^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053868261 10000000000 3862974596871 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21456331/50000000 : ℝ), (908198379/2000000000 : ℝ), (4053868261/10000000000 : ℝ)] ![(33277921633753/100000000000000 : ℝ), (7163656314407/20000000000000 : ℝ), (3862974596871/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21456331/50000000 : ℝ)|^4431 ≤ (33277921633753/100000000000000 : ℝ)^3407
        have hw : |(21456331/50000000 : ℝ)|=(21456331/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908198379/2000000000 : ℝ)|^4431 ≤ (7163656314407/20000000000000 : ℝ)^3407
        have hw : |(908198379/2000000000 : ℝ)|=(908198379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4053868261/10000000000 : ℝ)|^4431 ≤ (3862974596871/12500000000000 : ℝ)^3407
        have hw : |(4053868261/10000000000 : ℝ)|=(4053868261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10729/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (967/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1341/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1341/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1341/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1341/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1341/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1341/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1341/12500 : ℝ) ^ (4429/1024 : ℝ) ≤ (6409207115115327/100000000000000000000 : ℝ) := by
    have hpowers : (1341/12500 : ℝ)^4429 ≤ (6409207115115327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1341 : ℕ)^4429*100000000000000000000^1024 ≤ 6409207115115327^1024*12500^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1341 12500 6409207115115327 100000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1341/12500 : ℝ)) (X := (6409207115115327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4429/1024 : ℝ) ≤ (6250329713439707/20000000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4429 ≤ (6250329713439707/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4429*20000000000000000000^1024 ≤ 6250329713439707^1024*50000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 6250329713439707 20000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (6250329713439707/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006409207115115327/50000000000000000000 : ℝ) ≤ (10000296351534217/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50006409207115115327/50000000000000000000 : ℝ)^1024 ≤ (10000296351534217/10000000000000000 : ℝ)^4429 := by
      have hnat : (50006409207115115327 : ℕ)^1024*10000000000000000^4429 ≤ 10000296351534217^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006409207115115327 50000000000000000000 10000296351534217 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000296351534217/10000000000000000 : ℝ)) (X := (50006409207115115327/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018830427841156931/50000000000000000000 : ℝ) ≤ (2500217651470611/2500000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50018830427841156931/50000000000000000000 : ℝ)^1024 ≤ (2500217651470611/2500000000000000 : ℝ)^4429 := by
      have hnat : (50018830427841156931 : ℕ)^1024*2500000000000000^4429 ≤ 2500217651470611^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018830427841156931 50000000000000000000 2500217651470611 2500000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500217651470611/2500000000000000 : ℝ)) (X := (50018830427841156931/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006250329713439707/10000000000000000000 : ℝ) ≤ (10001444860230671/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (10006250329713439707/10000000000000000000 : ℝ)^1024 ≤ (10001444860230671/10000000000000000 : ℝ)^4429 := by
      have hnat : (10006250329713439707 : ℕ)^1024*10000000000000000^4429 ≤ 10001444860230671^4429*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006250329713439707 10000000000000000000 10001444860230671 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001444860230671/10000000000000000 : ℝ)) (X := (10006250329713439707/10000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6409207115115327/100000000000000000000 : ℝ) ≤ ((225948025157551597/226000000000000000 : ℝ)+2*(82036335461/67800000000000 : ℝ)*(1341/12500 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (225948025157551597/226000000000000000 : ℝ)+2*(82036335461/67800000000000 : ℝ)*(1341/12500 : ℝ)=(10000296351534217/10000000000000000 : ℝ) by norm_num, show 1+2*(6409207115115327/100000000000000000000 : ℝ)=(50006409207115115327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6250329713439707/20000000000000000000 : ℝ)+(6409207115115327/100000000000000000000 : ℝ) ≤ ((225948025157551597/226000000000000000 : ℝ)+(82036335461/67800000000000 : ℝ)*((7737/50000 : ℝ)+(1341/12500 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (225948025157551597/226000000000000000 : ℝ)+(82036335461/67800000000000 : ℝ)*((7737/50000 : ℝ)+(1341/12500 : ℝ))=(2500217651470611/2500000000000000 : ℝ) by norm_num, show 1+(6250329713439707/20000000000000000000 : ℝ)+(6409207115115327/100000000000000000000 : ℝ)=(50018830427841156931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6250329713439707/20000000000000000000 : ℝ) ≤ ((225948025157551597/226000000000000000 : ℝ)+2*(82036335461/67800000000000 : ℝ)*(7737/50000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (225948025157551597/226000000000000000 : ℝ)+2*(82036335461/67800000000000 : ℝ)*(7737/50000 : ℝ)=(10001444860230671/10000000000000000 : ℝ) by norm_num, show 1+2*(6250329713439707/20000000000000000000 : ℝ)=(10006250329713439707/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (225948025157551597/226000000000000000 : ℝ)*(X 1 0+X 2 0)+(82036335461/67800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (225948025157551597/226000000000000000 : ℝ)) (alpha := (82036335461/67800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (225948025157551597/226000000000000000 : ℝ)*(X 0 1+X 2 1)+(82036335461/67800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (225948025157551597/226000000000000000 : ℝ)) (alpha := (82036335461/67800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (225948025157551597/226000000000000000 : ℝ)*(X 0 2+X 1 2)+(82036335461/67800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (1341/12500 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (225948025157551597/226000000000000000 : ℝ)) (alpha := (82036335461/67800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1936602207/10000000000 : ℝ)*X 0 0+(217566091/400000000 : ℝ)*X 0 1+(1043003993/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214158781/400000000 : ℝ)*X 1 0+(-102575089/500000000 : ℝ)*X 1 1+(5215020011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669246181/1250000000 : ℝ)*X 2 0+(5215019957/10000000000 : ℝ)*X 2 1+(-410300391/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4291198637/10000000000 : ℝ)*X 0 0+(4051337687/10000000000 : ℝ)*X 0 1+(4543503603/10000000000 : ℝ)*X 0 2+(4291198637/10000000000 : ℝ)*X 1 0+(4051337687/10000000000 : ℝ)*X 1 1+(4543503603/10000000000 : ℝ)*X 1 2+(4291198637/10000000000 : ℝ)*X 2 0+(4051337687/10000000000 : ℝ)*X 2 1+(4543503603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-38732663/200000000 : ℝ)*X 0 0+(2608081877/5000000000 : ℝ)*X 0 1+(54380001/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295567763/10000000000 : ℝ)*X 1 0+(-1828521489/10000000000 : ℝ)*X 1 1+(5438000523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647784021/5000000000 : ℝ)*X 2 0+(5438000059/10000000000 : ℝ)*X 2 1+(-1828521749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((21456331/50000000 : ℝ)*X 0 0+(908198379/2000000000 : ℝ)*X 0 1+(4053868261/10000000000 : ℝ)*X 0 2+(21456331/50000000 : ℝ)*X 1 0+(908198379/2000000000 : ℝ)*X 1 1+(4053868261/10000000000 : ℝ)*X 1 2+(21456331/50000000 : ℝ)*X 2 0+(908198379/2000000000 : ℝ)*X 2 1+(4053868261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33389249215843625853150339/2825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2182614929/100000000000000 : ℝ)*(base19) + (992096347/50000000000000 : ℝ)*(base23) + (71879451/100000000000000 : ℝ)*(lower2) + (389697771/100000000000000 : ℝ)*(upper3) + (58729197/50000000000000 : ℝ)*(upper5) + (1623396117314571/50000000000000 : ℝ)*(major0) + (1623396117314571/50000000000000 : ℝ)*(major1) + (1623396117314571/50000000000000 : ℝ)*(major2) + (2230843579423807/50000000000000 : ℝ)*(sp0) + (4461715257091801/100000000000000 : ℝ)*(sp1) + (1115428863878509/25000000000000 : ℝ)*(sp2) + (2031849236822923/100000000000000 : ℝ)*(sp3) + (30280859117/100000000000000 : ℝ)*(sp4) + (869937759/5000000000000 : ℝ)*(sp7) + (2031866635578103/100000000000000 : ℝ)*(f.failure) + (446171743970673/10000000000000 : ℝ)*(f.sum) + (24752036059/282500000000000000000000000 : ℝ)*base66 + (10997105286510113/11300000000000000000000000000000 : ℝ)*base68 + (309375376489887/11300000000000000000000000000000 : ℝ)*base69 + (9524777174389887/11300000000000000000000000000000 : ℝ)*base71 + (537948090303/141250000000000000000000000 : ℝ)*base73 + (89076473385189887/11300000000000000000000000000000 : ℝ)*base75 + (18589551260489887/11300000000000000000000000000000 : ℝ)*base77 + (87410646674289887/11300000000000000000000000000000 : ℝ)*base79 + (165781474199/70625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (10780229/1000000000000000000000 : ℝ)*base90 + (10780229/1000000000000000000000 : ℝ)*base92 + (10780229/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50740111465270284726643503/5650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1191259717/100000000000000 : ℝ)*(base19) + (1413659743/100000000000000 : ℝ)*(base23) + (125000157/25000000000000 : ℝ)*(lower1) + (5062489/20000000000000 : ℝ)*(upper2) + (4278617/4000000000000 : ℝ)*(upper3) + (37051397/20000000000000 : ℝ)*(upper5) + (1640166024359433/50000000000000 : ℝ)*(major0) + (1640166024359433/50000000000000 : ℝ)*(major1) + (1640166024359433/50000000000000 : ℝ)*(major2) + (1425761771/25000000000000 : ℝ)*(sp1) + (4507807698357573/100000000000000 : ℝ)*(sp4) + (4507800804050771/100000000000000 : ℝ)*(sp5) + (450780628469783/10000000000000 : ℝ)*(sp6) + (102642804986423/5000000000000 : ℝ)*(sp7) + (102642804986423/5000000000000 : ℝ)*(f.failure) + (4507807698357573/100000000000000 : ℝ)*(f.sum) + (1500926434621/565000000000000000000000000 : ℝ)*base65 + (97217253365274501/11300000000000000000000000000000 : ℝ)*base67 + (329881214818125499/11300000000000000000000000000000 : ℝ)*base70 + (52582571065025499/11300000000000000000000000000000 : ℝ)*base72 + (1275970533453/282500000000000000000000000 : ℝ)*base73 + (30114254597774501/11300000000000000000000000000000 : ℝ)*base75 + (76038415968125499/11300000000000000000000000000000 : ℝ)*base78 + (46554487721125499/11300000000000000000000000000000 : ℝ)*base80 + (6134255497479/565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (270011/50000000000000000000 : ℝ)*base89 + (270011/50000000000000000000 : ℝ)*base91 + (270011/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1467_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10729/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (967/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1467_s7_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936605717/10000000000 : ℝ)*x 0 + (217565629/400000000 : ℝ)*x 1 + (1043005811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936605717/10000000000 : ℝ)^4431 ≤ (1477971249371/12500000000000 : ℝ)^3407 := by
    have hnat : (1936605717 : ℕ)^4431*12500000000000^3407 ≤ 1477971249371^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936605717 10000000000 1477971249371 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217565629/400000000 : ℝ)^4431 ≤ (45294127228347/100000000000000 : ℝ)^3407 := by
    have hnat : (217565629 : ℕ)^4431*100000000000000^3407 ≤ 45294127228347^3407*400000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217565629 400000000 45294127228347 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043005811/2000000000 : ℝ)^4431 ≤ (42882102755613/100000000000000 : ℝ)^3407 := by
    have hnat : (1043005811 : ℕ)^4431*100000000000000^3407 ≤ 42882102755613^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043005811 2000000000 42882102755613 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936605717/10000000000 : ℝ), (217565629/400000000 : ℝ), (1043005811/2000000000 : ℝ)] ![(1477971249371/12500000000000 : ℝ), (45294127228347/100000000000000 : ℝ), (42882102755613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936605717/10000000000 : ℝ)|^4431 ≤ (1477971249371/12500000000000 : ℝ)^3407
        have hw : |(-1936605717/10000000000 : ℝ)|=(1936605717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217565629/400000000 : ℝ)|^4431 ≤ (45294127228347/100000000000000 : ℝ)^3407
        have hw : |(217565629/400000000 : ℝ)|=(217565629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043005811/2000000000 : ℝ)|^4431 ≤ (42882102755613/100000000000000 : ℝ)^3407
        have hw : |(1043005811/2000000000 : ℝ)|=(1043005811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s7_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676982967/5000000000 : ℝ)*x 0 + (-2051494677/10000000000 : ℝ)*x 1 + (5215028997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676982967/5000000000 : ℝ)^4431 ≤ (5546729496641/12500000000000 : ℝ)^3407 := by
    have hnat : (2676982967 : ℕ)^4431*12500000000000^3407 ≤ 5546729496641^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676982967 5000000000 5546729496641 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051494677/10000000000 : ℝ)^4431 ≤ (2548812374943/20000000000000 : ℝ)^3407 := by
    have hnat : (2051494677 : ℕ)^4431*20000000000000^3407 ≤ 2548812374943^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051494677 10000000000 2548812374943 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215028997/10000000000 : ℝ)^4431 ≤ (42882102135349/100000000000000 : ℝ)^3407 := by
    have hnat : (5215028997 : ℕ)^4431*100000000000000^3407 ≤ 42882102135349^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215028997 10000000000 42882102135349 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676982967/5000000000 : ℝ), (-2051494677/10000000000 : ℝ), (5215028997/10000000000 : ℝ)] ![(5546729496641/12500000000000 : ℝ), (2548812374943/20000000000000 : ℝ), (42882102135349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676982967/5000000000 : ℝ)|^4431 ≤ (5546729496641/12500000000000 : ℝ)^3407
        have hw : |(2676982967/5000000000 : ℝ)|=(2676982967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051494677/10000000000 : ℝ)|^4431 ≤ (2548812374943/20000000000000 : ℝ)^3407
        have hw : |(-2051494677/10000000000 : ℝ)|=(2051494677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215028997/10000000000 : ℝ)|^4431 ≤ (42882102135349/100000000000000 : ℝ)^3407
        have hw : |(5215028997/10000000000 : ℝ)|=(5215028997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s7_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676982993/5000000000 : ℝ)*x 0 + (5215029169/10000000000 : ℝ)*x 1 + (-102574719/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676982993/5000000000 : ℝ)^4431 ≤ (44373836533639/100000000000000 : ℝ)^3407 := by
    have hnat : (2676982993 : ℕ)^4431*100000000000000^3407 ≤ 44373836533639^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676982993 5000000000 44373836533639 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215029169/10000000000 : ℝ)^4431 ≤ (21441051987377/50000000000000 : ℝ)^3407 := by
    have hnat : (5215029169 : ℕ)^4431*50000000000000^3407 ≤ 21441051987377^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215029169 10000000000 21441051987377 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102574719/500000000 : ℝ)^4431 ≤ (12744059475199/100000000000000 : ℝ)^3407 := by
    have hnat : (102574719 : ℕ)^4431*100000000000000^3407 ≤ 12744059475199^3407*500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102574719 500000000 12744059475199 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676982993/5000000000 : ℝ), (5215029169/10000000000 : ℝ), (-102574719/500000000 : ℝ)] ![(44373836533639/100000000000000 : ℝ), (21441051987377/50000000000000 : ℝ), (12744059475199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676982993/5000000000 : ℝ)|^4431 ≤ (44373836533639/100000000000000 : ℝ)^3407
        have hw : |(2676982993/5000000000 : ℝ)|=(2676982993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215029169/10000000000 : ℝ)|^4431 ≤ (21441051987377/50000000000000 : ℝ)^3407
        have hw : |(5215029169/10000000000 : ℝ)|=(5215029169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102574719/500000000 : ℝ)|^4431 ≤ (12744059475199/100000000000000 : ℝ)^3407
        have hw : |(-102574719/500000000 : ℝ)|=(102574719/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s7_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072799971/2500000000 : ℝ)*x 0 + (4051360109/10000000000 : ℝ)*x 1 + (1135870179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072799971/2500000000 : ℝ)^4431 ≤ (33277252800789/100000000000000 : ℝ)^3407 := by
    have hnat : (1072799971 : ℕ)^4431*100000000000000^3407 ≤ 33277252800789^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072799971 2500000000 33277252800789 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051360109/10000000000 : ℝ)^4431 ≤ (3859866494591/12500000000000 : ℝ)^3407 := by
    have hnat : (4051360109 : ℕ)^4431*12500000000000^3407 ≤ 3859866494591^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051360109 10000000000 3859866494591 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135870179/2500000000 : ℝ)^4431 ≤ (35843815231553/100000000000000 : ℝ)^3407 := by
    have hnat : (1135870179 : ℕ)^4431*100000000000000^3407 ≤ 35843815231553^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135870179 2500000000 35843815231553 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072799971/2500000000 : ℝ), (4051360109/10000000000 : ℝ), (1135870179/2500000000 : ℝ)] ![(33277252800789/100000000000000 : ℝ), (3859866494591/12500000000000 : ℝ), (35843815231553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072799971/2500000000 : ℝ)|^4431 ≤ (33277252800789/100000000000000 : ℝ)^3407
        have hw : |(1072799971/2500000000 : ℝ)|=(1072799971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4051360109/10000000000 : ℝ)|^4431 ≤ (3859866494591/12500000000000 : ℝ)^3407
        have hw : |(4051360109/10000000000 : ℝ)|=(4051360109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135870179/2500000000 : ℝ)|^4431 ≤ (35843815231553/100000000000000 : ℝ)^3407
        have hw : |(1135870179/2500000000 : ℝ)|=(1135870179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s7_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936636859/10000000000 : ℝ)*x 0 + (5216172521/10000000000 : ℝ)*x 1 + (5437988723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936636859/10000000000 : ℝ)^4431 ≤ (73900107979/625000000000 : ℝ)^3407 := by
    have hnat : (1936636859 : ℕ)^4431*625000000000^3407 ≤ 73900107979^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936636859 10000000000 73900107979 625000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216172521/10000000000 : ℝ)^4431 ≤ (42894331631079/100000000000000 : ℝ)^3407 := by
    have hnat : (5216172521 : ℕ)^4431*100000000000000^3407 ≤ 42894331631079^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216172521 10000000000 42894331631079 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437988723/10000000000 : ℝ)^4431 ≤ (353762899041/781250000000 : ℝ)^3407 := by
    have hnat : (5437988723 : ℕ)^4431*781250000000^3407 ≤ 353762899041^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437988723 10000000000 353762899041 781250000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936636859/10000000000 : ℝ), (5216172521/10000000000 : ℝ), (5437988723/10000000000 : ℝ)] ![(73900107979/625000000000 : ℝ), (42894331631079/100000000000000 : ℝ), (353762899041/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936636859/10000000000 : ℝ)|^4431 ≤ (73900107979/625000000000 : ℝ)^3407
        have hw : |(-1936636859/10000000000 : ℝ)|=(1936636859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216172521/10000000000 : ℝ)|^4431 ≤ (42894331631079/100000000000000 : ℝ)^3407
        have hw : |(5216172521/10000000000 : ℝ)|=(5216172521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437988723/10000000000 : ℝ)|^4431 ≤ (353762899041/781250000000 : ℝ)^3407
        have hw : |(5437988723/10000000000 : ℝ)|=(5437988723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s7_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291267729/10000000000 : ℝ)*x 0 + (4540969523/10000000000 : ℝ)*x 1 + (2026944927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291267729/10000000000 : ℝ)^4431 ≤ (33277937054587/100000000000000 : ℝ)^3407 := by
    have hnat : (4291267729 : ℕ)^4431*100000000000000^3407 ≤ 33277937054587^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291267729 10000000000 33277937054587 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540969523/10000000000 : ℝ)^4431 ≤ (17909026034581/50000000000000 : ℝ)^3407 := by
    have hnat : (4540969523 : ℕ)^4431*50000000000000^3407 ≤ 17909026034581^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540969523 10000000000 17909026034581 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026944927/5000000000 : ℝ)^4431 ≤ (15452005429717/50000000000000 : ℝ)^3407 := by
    have hnat : (2026944927 : ℕ)^4431*50000000000000^3407 ≤ 15452005429717^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026944927 5000000000 15452005429717 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291267729/10000000000 : ℝ), (4540969523/10000000000 : ℝ), (2026944927/5000000000 : ℝ)] ![(33277937054587/100000000000000 : ℝ), (17909026034581/50000000000000 : ℝ), (15452005429717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291267729/10000000000 : ℝ)|^4431 ≤ (33277937054587/100000000000000 : ℝ)^3407
        have hw : |(4291267729/10000000000 : ℝ)|=(4291267729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540969523/10000000000 : ℝ)|^4431 ≤ (17909026034581/50000000000000 : ℝ)^3407
        have hw : |(4540969523/10000000000 : ℝ)|=(4540969523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2026944927/5000000000 : ℝ)|^4431 ≤ (15452005429717/50000000000000 : ℝ)^3407
        have hw : |(2026944927/5000000000 : ℝ)|=(2026944927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10729/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1073/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (967/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10729/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10729/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10729/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10729/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10729/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10729/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10729/100000 : ℝ) ^ (4429/1024 : ℝ) ≤ (6411791508200857/100000000000000000000 : ℝ) := by
    have hpowers : (10729/100000 : ℝ)^4429 ≤ (6411791508200857/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10729 : ℕ)^4429*100000000000000000000^1024 ≤ 6411791508200857^1024*100000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10729 100000 6411791508200857 100000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10729/100000 : ℝ)) (X := (6411791508200857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (967/6250 : ℝ) ^ (4429/1024 : ℝ) ≤ (15617090895959381/50000000000000000000 : ℝ) := by
    have hpowers : (967/6250 : ℝ)^4429 ≤ (15617090895959381/50000000000000000000 : ℝ)^1024 := by
      have hnat : (967 : ℕ)^4429*50000000000000000000^1024 ≤ 15617090895959381^1024*6250^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        967 6250 15617090895959381 50000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (967/6250 : ℝ)) (X := (15617090895959381/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006411791508200857/50000000000000000000 : ℝ) ≤ (10000296471026549/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50006411791508200857/50000000000000000000 : ℝ)^1024 ≤ (10000296471026549/10000000000000000 : ℝ)^4429 := by
      have hnat : (50006411791508200857 : ℕ)^1024*10000000000000000^4429 ≤ 10000296471026549^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006411791508200857 50000000000000000000 10000296471026549 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000296471026549/10000000000000000 : ℝ)) (X := (50006411791508200857/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037645973300119619/100000000000000000000 : ℝ) ≤ (1250108782737029/1250000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (100037645973300119619/100000000000000000000 : ℝ)^1024 ≤ (1250108782737029/1250000000000000 : ℝ)^4429 := by
      have hnat : (100037645973300119619 : ℕ)^1024*1250000000000000^4429 ≤ 1250108782737029^4429*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037645973300119619 100000000000000000000 1250108782737029 1250000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250108782737029/1250000000000000 : ℝ)) (X := (100037645973300119619/100000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015617090895959381/25000000000000000000 : ℝ) ≤ (2000288810553183/2000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (25015617090895959381/25000000000000000000 : ℝ)^1024 ≤ (2000288810553183/2000000000000000 : ℝ)^4429 := by
      have hnat : (25015617090895959381 : ℕ)^1024*2000000000000000^4429 ≤ 2000288810553183^4429*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015617090895959381 25000000000000000000 2000288810553183 2000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000288810553183/2000000000000000 : ℝ)) (X := (25015617090895959381/25000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6411791508200857/100000000000000000000 : ℝ) ≤ ((89979305042879059/90000000000000000 : ℝ)+2*(1088787229/900000000000 : ℝ)*(10729/100000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (89979305042879059/90000000000000000 : ℝ)+2*(1088787229/900000000000 : ℝ)*(10729/100000 : ℝ)=(10000296471026549/10000000000000000 : ℝ) by norm_num, show 1+2*(6411791508200857/100000000000000000000 : ℝ)=(50006411791508200857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15617090895959381/50000000000000000000 : ℝ)+(6411791508200857/100000000000000000000 : ℝ) ≤ ((89979305042879059/90000000000000000 : ℝ)+(1088787229/900000000000 : ℝ)*((967/6250 : ℝ)+(10729/100000 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (89979305042879059/90000000000000000 : ℝ)+(1088787229/900000000000 : ℝ)*((967/6250 : ℝ)+(10729/100000 : ℝ))=(1250108782737029/1250000000000000 : ℝ) by norm_num, show 1+(15617090895959381/50000000000000000000 : ℝ)+(6411791508200857/100000000000000000000 : ℝ)=(100037645973300119619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15617090895959381/50000000000000000000 : ℝ) ≤ ((89979305042879059/90000000000000000 : ℝ)+2*(1088787229/900000000000 : ℝ)*(967/6250 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (89979305042879059/90000000000000000 : ℝ)+2*(1088787229/900000000000 : ℝ)*(967/6250 : ℝ)=(2000288810553183/2000000000000000 : ℝ) by norm_num, show 1+2*(15617090895959381/50000000000000000000 : ℝ)=(25015617090895959381/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89979305042879059/90000000000000000 : ℝ)*(X 1 0+X 2 0)+(1088787229/900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (10729/100000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (89979305042879059/90000000000000000 : ℝ)) (alpha := (1088787229/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89979305042879059/90000000000000000 : ℝ)*(X 0 1+X 2 1)+(1088787229/900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (10729/100000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (89979305042879059/90000000000000000 : ℝ)) (alpha := (1088787229/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89979305042879059/90000000000000000 : ℝ)*(X 0 2+X 1 2)+(1088787229/900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (10729/100000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (89979305042879059/90000000000000000 : ℝ)) (alpha := (1088787229/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1936605717/10000000000 : ℝ)*X 0 0+(217565629/400000000 : ℝ)*X 0 1+(1043005811/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676982967/5000000000 : ℝ)*X 1 0+(-2051494677/10000000000 : ℝ)*X 1 1+(5215028997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676982993/5000000000 : ℝ)*X 2 0+(5215029169/10000000000 : ℝ)*X 2 1+(-102574719/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072799971/2500000000 : ℝ)*X 0 0+(4051360109/10000000000 : ℝ)*X 0 1+(1135870179/2500000000 : ℝ)*X 0 2+(1072799971/2500000000 : ℝ)*X 1 0+(4051360109/10000000000 : ℝ)*X 1 1+(1135870179/2500000000 : ℝ)*X 1 2+(1072799971/2500000000 : ℝ)*X 2 0+(4051360109/10000000000 : ℝ)*X 2 1+(1135870179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1936636859/10000000000 : ℝ)*X 0 0+(5216172521/10000000000 : ℝ)*X 0 1+(5437988723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4291267729/10000000000 : ℝ)*X 0 0+(4540969523/10000000000 : ℝ)*X 0 1+(2026944927/5000000000 : ℝ)*X 0 2+(4291267729/10000000000 : ℝ)*X 1 0+(4540969523/10000000000 : ℝ)*X 1 1+(2026944927/5000000000 : ℝ)*X 1 2+(4291267729/10000000000 : ℝ)*X 2 0+(4540969523/10000000000 : ℝ)*X 2 1+(2026944927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (455913188062359162112803/125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (802460311/100000000000000 : ℝ)*(base19) + (346182081/50000000000000 : ℝ)*(base23) + (10268493/12500000000000 : ℝ)*(lower2) + (15698013/100000000000000 : ℝ)*(upper3) + (184658083/100000000000000 : ℝ)*(upper5) + (1623529881830349/50000000000000 : ℝ)*(major0) + (1623529881830349/50000000000000 : ℝ)*(major1) + (1623529881830349/50000000000000 : ℝ)*(major2) + (2231034995810631/50000000000000 : ℝ)*(sp0) + (1115521136514021/25000000000000 : ℝ)*(sp1) + (4462084656152233/100000000000000 : ℝ)*(sp2) + (203202870238431/10000000000000 : ℝ)*(sp3) + (15356895133/100000000000000 : ℝ)*(sp4) + (1338710959/25000000000000 : ℝ)*(sp5) + (1016017028614073/50000000000000 : ℝ)*(f.failure) + (892417069703279/20000000000000 : ℝ)*(f.sum) + (20902437623/5000000000000000000000000 : ℝ)*base65 + (1291748242262399/500000000000000000000000000000 : ℝ)*base67 + (163086636262399/500000000000000000000000000000 : ℝ)*base69 + (658250402762399/500000000000000000000000000000 : ℝ)*base71 + (2289223447/1250000000000000000000000 : ℝ)*base73 + (855629046762399/500000000000000000000000000000 : ℝ)*base75 + (3992998261762399/500000000000000000000000000000 : ℝ)*base77 + (1131326324737601/500000000000000000000000000000 : ℝ)*base80 + (8032603641/2500000000000000000000000 : ℝ)*base82 + (2308939/500000000000000000000 : ℝ)*base90 + (2308939/500000000000000000000 : ℝ)*base92 + (2308939/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1467_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10729/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (967/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1467_box_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214319581/1250000000 : ℝ)*x 0 + (2703858279/5000000000 : ℝ)*x 1 + (5407714951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214319581/1250000000 : ℝ)^4431 ≤ (403673543313/4000000000000 : ℝ)^3407 := by
    have hnat : (214319581 : ℕ)^4431*4000000000000^3407 ≤ 403673543313^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214319581 1250000000 403673543313 4000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703858279/5000000000 : ℝ)^4431 ≤ (1798163575399/4000000000000 : ℝ)^3407 := by
    have hnat : (2703858279 : ℕ)^4431*4000000000000^3407 ≤ 1798163575399^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703858279 5000000000 1798163575399 4000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407714951/10000000000 : ℝ)^4431 ≤ (44954072010937/100000000000000 : ℝ)^3407 := by
    have hnat : (5407714951 : ℕ)^4431*100000000000000^3407 ≤ 44954072010937^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407714951 10000000000 44954072010937 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214319581/1250000000 : ℝ), (2703858279/5000000000 : ℝ), (5407714951/10000000000 : ℝ)] ![(403673543313/4000000000000 : ℝ), (1798163575399/4000000000000 : ℝ), (44954072010937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214319581/1250000000 : ℝ)|^4431 ≤ (403673543313/4000000000000 : ℝ)^3407
        have hw : |(-214319581/1250000000 : ℝ)|=(214319581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703858279/5000000000 : ℝ)|^4431 ≤ (1798163575399/4000000000000 : ℝ)^3407
        have hw : |(2703858279/5000000000 : ℝ)|=(2703858279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407714951/10000000000 : ℝ)|^4431 ≤ (44954072010937/100000000000000 : ℝ)^3407
        have hw : |(5407714951/10000000000 : ℝ)|=(5407714951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317483209/2500000000 : ℝ)*x 0 + (-1905293261/10000000000 : ℝ)*x 1 + (54077153/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317483209/2500000000 : ℝ)^4431 ≤ (43470182341069/100000000000000 : ℝ)^3407 := by
    have hnat : (1317483209 : ℕ)^4431*100000000000000^3407 ≤ 43470182341069^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317483209 2500000000 43470182341069 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1905293261/10000000000 : ℝ)^4431 ≤ (11575741854823/100000000000000 : ℝ)^3407 := by
    have hnat : (1905293261 : ℕ)^4431*100000000000000^3407 ≤ 11575741854823^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905293261 10000000000 11575741854823 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54077153/100000000 : ℝ)^4431 ≤ (44954075784141/100000000000000 : ℝ)^3407 := by
    have hnat : (54077153 : ℕ)^4431*100000000000000^3407 ≤ 44954075784141^3407*100000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54077153 100000000 44954075784141 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317483209/2500000000 : ℝ), (-1905293261/10000000000 : ℝ), (54077153/100000000 : ℝ)] ![(43470182341069/100000000000000 : ℝ), (11575741854823/100000000000000 : ℝ), (44954075784141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317483209/2500000000 : ℝ)|^4431 ≤ (43470182341069/100000000000000 : ℝ)^3407
        have hw : |(1317483209/2500000000 : ℝ)|=(1317483209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1905293261/10000000000 : ℝ)|^4431 ≤ (11575741854823/100000000000000 : ℝ)^3407
        have hw : |(-1905293261/10000000000 : ℝ)|=(1905293261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54077153/100000000 : ℝ)|^4431 ≤ (44954075784141/100000000000000 : ℝ)^3407
        have hw : |(54077153/100000000 : ℝ)|=(54077153/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317483109/2500000000 : ℝ)*x 0 + (1081543167/2000000000 : ℝ)*x 1 + (-119080817/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317483109/2500000000 : ℝ)^4431 ≤ (43470178049897/100000000000000 : ℝ)^3407 := by
    have hnat : (1317483109 : ℕ)^4431*100000000000000^3407 ≤ 43470178049897^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317483109 2500000000 43470178049897 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081543167/2000000000 : ℝ)^4431 ≤ (44954081568279/100000000000000 : ℝ)^3407 := by
    have hnat : (1081543167 : ℕ)^4431*100000000000000^3407 ≤ 44954081568279^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081543167 2000000000 44954081568279 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119080817/625000000 : ℝ)^4431 ≤ (2315148072283/20000000000000 : ℝ)^3407 := by
    have hnat : (119080817 : ℕ)^4431*20000000000000^3407 ≤ 2315148072283^3407*625000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119080817 625000000 2315148072283 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317483109/2500000000 : ℝ), (1081543167/2000000000 : ℝ), (-119080817/625000000 : ℝ)] ![(43470178049897/100000000000000 : ℝ), (44954081568279/100000000000000 : ℝ), (2315148072283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317483109/2500000000 : ℝ)|^4431 ≤ (43470178049897/100000000000000 : ℝ)^3407
        have hw : |(1317483109/2500000000 : ℝ)|=(1317483109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081543167/2000000000 : ℝ)|^4431 ≤ (44954081568279/100000000000000 : ℝ)^3407
        have hw : |(1081543167/2000000000 : ℝ)|=(1081543167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-119080817/625000000 : ℝ)|^4431 ≤ (2315148072283/20000000000000 : ℝ)^3407
        have hw : |(-119080817/625000000 : ℝ)|=(119080817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (899296169/2000000000 : ℝ)*x 0 + (4195850137/10000000000 : ℝ)*x 1 + (4195850431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899296169/2000000000 : ℝ)^4431 ≤ (1768116968127/5000000000000 : ℝ)^3407 := by
    have hnat : (899296169 : ℕ)^4431*5000000000000^3407 ≤ 1768116968127^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899296169 2000000000 1768116968127 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4195850137/10000000000 : ℝ)^4431 ≤ (32318828839041/100000000000000 : ℝ)^3407 := by
    have hnat : (4195850137 : ℕ)^4431*100000000000000^3407 ≤ 32318828839041^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195850137 10000000000 32318828839041 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4195850431/10000000000 : ℝ)^4431 ≤ (16159415892113/50000000000000 : ℝ)^3407 := by
    have hnat : (4195850431 : ℕ)^4431*50000000000000^3407 ≤ 16159415892113^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195850431 10000000000 16159415892113 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899296169/2000000000 : ℝ), (4195850137/10000000000 : ℝ), (4195850431/10000000000 : ℝ)] ![(1768116968127/5000000000000 : ℝ), (32318828839041/100000000000000 : ℝ), (16159415892113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899296169/2000000000 : ℝ)|^4431 ≤ (1768116968127/5000000000000 : ℝ)^3407
        have hw : |(899296169/2000000000 : ℝ)|=(899296169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4195850137/10000000000 : ℝ)|^4431 ≤ (32318828839041/100000000000000 : ℝ)^3407
        have hw : |(4195850137/10000000000 : ℝ)|=(4195850137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4195850431/10000000000 : ℝ)|^4431 ≤ (16159415892113/50000000000000 : ℝ)^3407
        have hw : |(4195850431/10000000000 : ℝ)|=(4195850431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164125317/10000000000 : ℝ)*x 0 + (5241862041/10000000000 : ℝ)*x 1 + (1048372357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164125317/10000000000 : ℝ)^4431 ≤ (13661438478751/100000000000000 : ℝ)^3407 := by
    have hnat : (2164125317 : ℕ)^4431*100000000000000^3407 ≤ 13661438478751^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164125317 10000000000 13661438478751 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241862041/10000000000 : ℝ)^4431 ≤ (43169282126961/100000000000000 : ℝ)^3407 := by
    have hnat : (5241862041 : ℕ)^4431*100000000000000^3407 ≤ 43169282126961^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241862041 10000000000 43169282126961 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048372357/2000000000 : ℝ)^4431 ≤ (5396159923127/12500000000000 : ℝ)^3407 := by
    have hnat : (1048372357 : ℕ)^4431*12500000000000^3407 ≤ 5396159923127^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048372357 2000000000 5396159923127 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164125317/10000000000 : ℝ), (5241862041/10000000000 : ℝ), (1048372357/2000000000 : ℝ)] ![(13661438478751/100000000000000 : ℝ), (43169282126961/100000000000000 : ℝ), (5396159923127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164125317/10000000000 : ℝ)|^4431 ≤ (13661438478751/100000000000000 : ℝ)^3407
        have hw : |(-2164125317/10000000000 : ℝ)|=(2164125317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241862041/10000000000 : ℝ)|^4431 ≤ (43169282126961/100000000000000 : ℝ)^3407
        have hw : |(5241862041/10000000000 : ℝ)|=(5241862041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048372357/2000000000 : ℝ)|^4431 ≤ (5396159923127/12500000000000 : ℝ)^3407
        have hw : |(1048372357/2000000000 : ℝ)|=(1048372357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385812871/10000000000 : ℝ)*x 0 + (-246620789/1250000000 : ℝ)*x 1 + (5241861597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385812871/10000000000 : ℝ)^4431 ≤ (44717422529007/100000000000000 : ℝ)^3407 := by
    have hnat : (5385812871 : ℕ)^4431*100000000000000^3407 ≤ 44717422529007^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385812871 10000000000 44717422529007 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246620789/1250000000 : ℝ)^4431 ≤ (3028325022361/25000000000000 : ℝ)^3407 := by
    have hnat : (246620789 : ℕ)^4431*25000000000000^3407 ≤ 3028325022361^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246620789 1250000000 3028325022361 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241861597/10000000000 : ℝ)^4431 ≤ (215846386857/500000000000 : ℝ)^3407 := by
    have hnat : (5241861597 : ℕ)^4431*500000000000^3407 ≤ 215846386857^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241861597 10000000000 215846386857 500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385812871/10000000000 : ℝ), (-246620789/1250000000 : ℝ), (5241861597/10000000000 : ℝ)] ![(44717422529007/100000000000000 : ℝ), (3028325022361/25000000000000 : ℝ), (215846386857/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385812871/10000000000 : ℝ)|^4431 ≤ (44717422529007/100000000000000 : ℝ)^3407
        have hw : |(5385812871/10000000000 : ℝ)|=(5385812871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246620789/1250000000 : ℝ)|^4431 ≤ (3028325022361/25000000000000 : ℝ)^3407
        have hw : |(-246620789/1250000000 : ℝ)|=(246620789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241861597/10000000000 : ℝ)|^4431 ≤ (215846386857/500000000000 : ℝ)^3407
        have hw : |(5241861597/10000000000 : ℝ)|=(5241861597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385812929/10000000000 : ℝ)*x 0 + (5241861477/10000000000 : ℝ)*x 1 + (-986483197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385812929/10000000000 : ℝ)^4431 ≤ (11179355788827/25000000000000 : ℝ)^3407 := by
    have hnat : (5385812929 : ℕ)^4431*25000000000000^3407 ≤ 11179355788827^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385812929 10000000000 11179355788827 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241861477/10000000000 : ℝ)^4431 ≤ (43169276086113/100000000000000 : ℝ)^3407 := by
    have hnat : (5241861477 : ℕ)^4431*100000000000000^3407 ≤ 43169276086113^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241861477 10000000000 43169276086113 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986483197/5000000000 : ℝ)^4431 ≤ (1211330074421/10000000000000 : ℝ)^3407 := by
    have hnat : (986483197 : ℕ)^4431*10000000000000^3407 ≤ 1211330074421^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986483197 5000000000 1211330074421 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385812929/10000000000 : ℝ), (5241861477/10000000000 : ℝ), (-986483197/5000000000 : ℝ)] ![(11179355788827/25000000000000 : ℝ), (43169276086113/100000000000000 : ℝ), (1211330074421/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385812929/10000000000 : ℝ)|^4431 ≤ (11179355788827/25000000000000 : ℝ)^3407
        have hw : |(5385812929/10000000000 : ℝ)|=(5385812929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241861477/10000000000 : ℝ)|^4431 ≤ (43169276086113/100000000000000 : ℝ)^3407
        have hw : |(5241861477/10000000000 : ℝ)|=(5241861477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986483197/5000000000 : ℝ)|^4431 ≤ (1211330074421/10000000000000 : ℝ)^3407
        have hw : |(-986483197/5000000000 : ℝ)|=(986483197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4083724579/10000000000 : ℝ)*x 0 + (2201043929/5000000000 : ℝ)*x 1 + (550260973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4083724579/10000000000 : ℝ)^4431 ≤ (390001687339/1250000000000 : ℝ)^3407 := by
    have hnat : (4083724579 : ℕ)^4431*1250000000000^3407 ≤ 390001687339^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4083724579 10000000000 390001687339 1250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201043929/5000000000 : ℝ)^4431 ≤ (6879986574861/20000000000000 : ℝ)^3407 := by
    have hnat : (2201043929 : ℕ)^4431*20000000000000^3407 ≤ 6879986574861^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201043929 5000000000 6879986574861 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550260973/1250000000 : ℝ)^4431 ≤ (4299991515279/12500000000000 : ℝ)^3407 := by
    have hnat : (550260973 : ℕ)^4431*12500000000000^3407 ≤ 4299991515279^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550260973 1250000000 4299991515279 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4083724579/10000000000 : ℝ), (2201043929/5000000000 : ℝ), (550260973/1250000000 : ℝ)] ![(390001687339/1250000000000 : ℝ), (6879986574861/20000000000000 : ℝ), (4299991515279/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4083724579/10000000000 : ℝ)|^4431 ≤ (390001687339/1250000000000 : ℝ)^3407
        have hw : |(4083724579/10000000000 : ℝ)|=(4083724579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201043929/5000000000 : ℝ)|^4431 ≤ (6879986574861/20000000000000 : ℝ)^3407
        have hw : |(2201043929/5000000000 : ℝ)|=(2201043929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550260973/1250000000 : ℝ)|^4431 ≤ (4299991515279/12500000000000 : ℝ)^3407
        have hw : |(550260973/1250000000 : ℝ)|=(550260973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_8 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-517347337/2500000000 : ℝ)*x 0 + (5126187699/10000000000 : ℝ)*x 1 + (5428296741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517347337/2500000000 : ℝ)^4431 ≤ (644441260479/5000000000000 : ℝ)^3407 := by
    have hnat : (517347337 : ℕ)^4431*5000000000000^3407 ≤ 644441260479^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517347337 2500000000 644441260479 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126187699/10000000000 : ℝ)^4431 ≤ (5241807017781/12500000000000 : ℝ)^3407 := by
    have hnat : (5126187699 : ℕ)^4431*12500000000000^3407 ≤ 5241807017781^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126187699 10000000000 5241807017781 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428296741/10000000000 : ℝ)^4431 ≤ (22588359317363/50000000000000 : ℝ)^3407 := by
    have hnat : (5428296741 : ℕ)^4431*50000000000000^3407 ≤ 22588359317363^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428296741 10000000000 22588359317363 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517347337/2500000000 : ℝ), (5126187699/10000000000 : ℝ), (5428296741/10000000000 : ℝ)] ![(644441260479/5000000000000 : ℝ), (5241807017781/12500000000000 : ℝ), (22588359317363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517347337/2500000000 : ℝ)|^4431 ≤ (644441260479/5000000000000 : ℝ)^3407
        have hw : |(-517347337/2500000000 : ℝ)|=(517347337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126187699/10000000000 : ℝ)|^4431 ≤ (5241807017781/12500000000000 : ℝ)^3407
        have hw : |(5126187699/10000000000 : ℝ)|=(5126187699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428296741/10000000000 : ℝ)|^4431 ≤ (22588359317363/50000000000000 : ℝ)^3407
        have hw : |(5428296741/10000000000 : ℝ)|=(5428296741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_9 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627772523/5000000000 : ℝ)*x 0 + (-1896637181/10000000000 : ℝ)*x 1 + (1357074079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627772523/5000000000 : ℝ)^4431 ≤ (43315894481801/100000000000000 : ℝ)^3407 := by
    have hnat : (2627772523 : ℕ)^4431*100000000000000^3407 ≤ 43315894481801^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627772523 5000000000 43315894481801 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896637181/10000000000 : ℝ)^4431 ≤ (11507391471867/100000000000000 : ℝ)^3407 := by
    have hnat : (1896637181 : ℕ)^4431*100000000000000^3407 ≤ 11507391471867^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896637181 10000000000 11507391471867 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357074079/2500000000 : ℝ)^4431 ≤ (45176714034601/100000000000000 : ℝ)^3407 := by
    have hnat : (1357074079 : ℕ)^4431*100000000000000^3407 ≤ 45176714034601^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357074079 2500000000 45176714034601 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627772523/5000000000 : ℝ), (-1896637181/10000000000 : ℝ), (1357074079/2500000000 : ℝ)] ![(43315894481801/100000000000000 : ℝ), (11507391471867/100000000000000 : ℝ), (45176714034601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627772523/5000000000 : ℝ)|^4431 ≤ (43315894481801/100000000000000 : ℝ)^3407
        have hw : |(2627772523/5000000000 : ℝ)|=(2627772523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1896637181/10000000000 : ℝ)|^4431 ≤ (11507391471867/100000000000000 : ℝ)^3407
        have hw : |(-1896637181/10000000000 : ℝ)|=(1896637181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357074079/2500000000 : ℝ)|^4431 ≤ (45176714034601/100000000000000 : ℝ)^3407
        have hw : |(1357074079/2500000000 : ℝ)|=(1357074079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_10 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328471537/625000000 : ℝ)*x 0 + (5428296503/10000000000 : ℝ)*x 1 + (-1896637541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328471537/625000000 : ℝ)^4431 ≤ (43315889615321/100000000000000 : ℝ)^3407 := by
    have hnat : (328471537 : ℕ)^4431*100000000000000^3407 ≤ 43315889615321^3407*625000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328471537 625000000 43315889615321 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428296503/10000000000 : ℝ)^4431 ≤ (1411772376833/3125000000000 : ℝ)^3407 := by
    have hnat : (5428296503 : ℕ)^4431*3125000000000^3407 ≤ 1411772376833^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428296503 10000000000 1411772376833 3125000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896637541/10000000000 : ℝ)^4431 ≤ (11507394312563/100000000000000 : ℝ)^3407 := by
    have hnat : (1896637541 : ℕ)^4431*100000000000000^3407 ≤ 11507394312563^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896637541 10000000000 11507394312563 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328471537/625000000 : ℝ), (5428296503/10000000000 : ℝ), (-1896637541/10000000000 : ℝ)] ![(43315889615321/100000000000000 : ℝ), (1411772376833/3125000000000 : ℝ), (11507394312563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328471537/625000000 : ℝ)|^4431 ≤ (43315889615321/100000000000000 : ℝ)^3407
        have hw : |(328471537/625000000 : ℝ)|=(328471537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428296503/10000000000 : ℝ)|^4431 ≤ (1411772376833/3125000000000 : ℝ)^3407
        have hw : |(5428296503/10000000000 : ℝ)|=(5428296503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1896637541/10000000000 : ℝ)|^4431 ≤ (11507394312563/100000000000000 : ℝ)^3407
        have hw : |(-1896637541/10000000000 : ℝ)|=(1896637541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_11 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4546543193/10000000000 : ℝ)*x 0 + (4170226619/10000000000 : ℝ)*x 1 + (4170227087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4546543193/10000000000 : ℝ)^4431 ≤ (17937619995979/50000000000000 : ℝ)^3407 := by
    have hnat : (4546543193 : ℕ)^4431*50000000000000^3407 ≤ 17937619995979^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546543193 10000000000 17937619995979 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170226619/10000000000 : ℝ)^4431 ≤ (32062377660011/100000000000000 : ℝ)^3407 := by
    have hnat : (4170226619 : ℕ)^4431*100000000000000^3407 ≤ 32062377660011^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170226619 10000000000 32062377660011 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170227087/10000000000 : ℝ)^4431 ≤ (16031191169821/50000000000000 : ℝ)^3407 := by
    have hnat : (4170227087 : ℕ)^4431*50000000000000^3407 ≤ 16031191169821^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170227087 10000000000 16031191169821 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4546543193/10000000000 : ℝ), (4170226619/10000000000 : ℝ), (4170227087/10000000000 : ℝ)] ![(17937619995979/50000000000000 : ℝ), (32062377660011/100000000000000 : ℝ), (16031191169821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4546543193/10000000000 : ℝ)|^4431 ≤ (17937619995979/50000000000000 : ℝ)^3407
        have hw : |(4546543193/10000000000 : ℝ)|=(4546543193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170226619/10000000000 : ℝ)|^4431 ≤ (32062377660011/100000000000000 : ℝ)^3407
        have hw : |(4170226619/10000000000 : ℝ)|=(4170226619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170227087/10000000000 : ℝ)|^4431 ≤ (16031191169821/50000000000000 : ℝ)^3407
        have hw : |(4170227087/10000000000 : ℝ)|=(4170227087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_12 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-904752033/5000000000 : ℝ)*x 0 + (1379875643/2500000000 : ℝ)*x 1 + (1306721909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904752033/5000000000 : ℝ)^4431 ≤ (216492765019/2000000000000 : ℝ)^3407 := by
    have hnat : (904752033 : ℕ)^4431*2000000000000^3407 ≤ 216492765019^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904752033 5000000000 216492765019 2000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379875643/2500000000 : ℝ)^4431 ≤ (46166397439043/100000000000000 : ℝ)^3407 := by
    have hnat : (1379875643 : ℕ)^4431*100000000000000^3407 ≤ 46166397439043^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379875643 2500000000 46166397439043 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306721909/2500000000 : ℝ)^4431 ≤ (43008964297619/100000000000000 : ℝ)^3407 := by
    have hnat : (1306721909 : ℕ)^4431*100000000000000^3407 ≤ 43008964297619^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306721909 2500000000 43008964297619 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-904752033/5000000000 : ℝ), (1379875643/2500000000 : ℝ), (1306721909/2500000000 : ℝ)] ![(216492765019/2000000000000 : ℝ), (46166397439043/100000000000000 : ℝ), (43008964297619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-904752033/5000000000 : ℝ)|^4431 ≤ (216492765019/2000000000000 : ℝ)^3407
        have hw : |(-904752033/5000000000 : ℝ)|=(904752033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379875643/2500000000 : ℝ)|^4431 ≤ (46166397439043/100000000000000 : ℝ)^3407
        have hw : |(1379875643/2500000000 : ℝ)|=(1379875643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306721909/2500000000 : ℝ)|^4431 ≤ (43008964297619/100000000000000 : ℝ)^3407
        have hw : |(1306721909/2500000000 : ℝ)|=(1306721909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_13 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337267109/625000000 : ℝ)*x 0 + (-494722443/2500000000 : ℝ)*x 1 + (2613443849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337267109/625000000 : ℝ)^4431 ≤ (2801900941277/6250000000000 : ℝ)^3407 := by
    have hnat : (337267109 : ℕ)^4431*6250000000000^3407 ≤ 2801900941277^3407*625000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337267109 625000000 2801900941277 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494722443/2500000000 : ℝ)^4431 ≤ (380019374093/3125000000000 : ℝ)^3407 := by
    have hnat : (494722443 : ℕ)^4431*3125000000000^3407 ≤ 380019374093^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494722443 2500000000 380019374093 3125000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613443849/5000000000 : ℝ)^4431 ≤ (43008964961113/100000000000000 : ℝ)^3407 := by
    have hnat : (2613443849 : ℕ)^4431*100000000000000^3407 ≤ 43008964961113^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613443849 5000000000 43008964961113 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337267109/625000000 : ℝ), (-494722443/2500000000 : ℝ), (2613443849/5000000000 : ℝ)] ![(2801900941277/6250000000000 : ℝ), (380019374093/3125000000000 : ℝ), (43008964961113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337267109/625000000 : ℝ)|^4431 ≤ (2801900941277/6250000000000 : ℝ)^3407
        have hw : |(337267109/625000000 : ℝ)|=(337267109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494722443/2500000000 : ℝ)|^4431 ≤ (380019374093/3125000000000 : ℝ)^3407
        have hw : |(-494722443/2500000000 : ℝ)|=(494722443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613443849/5000000000 : ℝ)|^4431 ≤ (43008964961113/100000000000000 : ℝ)^3407
        have hw : |(2613443849/5000000000 : ℝ)|=(2613443849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_14 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539627361/1000000000 : ℝ)*x 0 + (2613443843/5000000000 : ℝ)*x 1 + (-123680623/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539627361/1000000000 : ℝ)^4431 ≤ (5603801701577/12500000000000 : ℝ)^3407 := by
    have hnat : (539627361 : ℕ)^4431*12500000000000^3407 ≤ 5603801701577^3407*1000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539627361 1000000000 5603801701577 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613443843/5000000000 : ℝ)^4431 ≤ (8601792966539/20000000000000 : ℝ)^3407 := by
    have hnat : (2613443843 : ℕ)^4431*20000000000000^3407 ≤ 8601792966539^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613443843 5000000000 8601792966539 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123680623/625000000 : ℝ)^4431 ≤ (6080310768719/50000000000000 : ℝ)^3407 := by
    have hnat : (123680623 : ℕ)^4431*50000000000000^3407 ≤ 6080310768719^3407*625000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123680623 625000000 6080310768719 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539627361/1000000000 : ℝ), (2613443843/5000000000 : ℝ), (-123680623/625000000 : ℝ)] ![(5603801701577/12500000000000 : ℝ), (8601792966539/20000000000000 : ℝ), (6080310768719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539627361/1000000000 : ℝ)|^4431 ≤ (5603801701577/12500000000000 : ℝ)^3407
        have hw : |(539627361/1000000000 : ℝ)|=(539627361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613443843/5000000000 : ℝ)|^4431 ≤ (8601792966539/20000000000000 : ℝ)^3407
        have hw : |(2613443843/5000000000 : ℝ)|=(2613443843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-123680623/625000000 : ℝ)|^4431 ≤ (6080310768719/50000000000000 : ℝ)^3407
        have hw : |(-123680623/625000000 : ℝ)|=(123680623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_box_15 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2022800581/5000000000 : ℝ)*x 0 + (4420685991/10000000000 : ℝ)*x 1 + (1105171633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022800581/5000000000 : ℝ)^4431 ≤ (3082185756301/10000000000000 : ℝ)^3407 := by
    have hnat : (2022800581 : ℕ)^4431*10000000000000^3407 ≤ 3082185756301^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022800581 5000000000 3082185756301 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4420685991/10000000000 : ℝ)^4431 ≤ (34589068452649/100000000000000 : ℝ)^3407 := by
    have hnat : (4420685991 : ℕ)^4431*100000000000000^3407 ≤ 34589068452649^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420685991 10000000000 34589068452649 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105171633/2500000000 : ℝ)^4431 ≤ (17294536978943/50000000000000 : ℝ)^3407 := by
    have hnat : (1105171633 : ℕ)^4431*50000000000000^3407 ≤ 17294536978943^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105171633 2500000000 17294536978943 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2022800581/5000000000 : ℝ), (4420685991/10000000000 : ℝ), (1105171633/2500000000 : ℝ)] ![(3082185756301/10000000000000 : ℝ), (34589068452649/100000000000000 : ℝ), (17294536978943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2022800581/5000000000 : ℝ)|^4431 ≤ (3082185756301/10000000000000 : ℝ)^3407
        have hw : |(2022800581/5000000000 : ℝ)|=(2022800581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4420685991/10000000000 : ℝ)|^4431 ≤ (34589068452649/100000000000000 : ℝ)^3407
        have hw : |(4420685991/10000000000 : ℝ)|=(4420685991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105171633/2500000000 : ℝ)|^4431 ≤ (17294536978943/50000000000000 : ℝ)^3407
        have hw : |(1105171633/2500000000 : ℝ)|=(1105171633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6369/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58417/100000 : ℝ) ∧ (79821/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21427/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1073/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1073/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1073/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1073/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1073/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1073/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1073/10000 : ℝ) ^ (4429/1024 : ℝ) ≤ (801797087797619/12500000000000000000 : ℝ) := by
    have hpowers : (1073/10000 : ℝ)^4429 ≤ (801797087797619/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1073 : ℕ)^4429*12500000000000000000^1024 ≤ 801797087797619^1024*10000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1073 10000 801797087797619 12500000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1073/10000 : ℝ)) (X := (801797087797619/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (967/6250 : ℝ) ^ (4429/1024 : ℝ) ≤ (15617090895959381/50000000000000000000 : ℝ) := by
    have hpowers : (967/6250 : ℝ)^4429 ≤ (15617090895959381/50000000000000000000 : ℝ)^1024 := by
      have hnat : (967 : ℕ)^4429*50000000000000000000^1024 ≤ 15617090895959381^1024*6250^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        967 6250 15617090895959381 50000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (967/6250 : ℝ)) (X := (15617090895959381/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250801797087797619/6250000000000000000 : ℝ) ≤ (2500074147638979/2500000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (6250801797087797619/6250000000000000000 : ℝ)^1024 ≤ (2500074147638979/2500000000000000 : ℝ)^4429 := by
      have hnat : (6250801797087797619 : ℕ)^1024*2500000000000000^4429 ≤ 2500074147638979^4429*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250801797087797619 6250000000000000000 2500074147638979 2500000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074147638979/2500000000000000 : ℝ)) (X := (6250801797087797619/6250000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018824279247149857/50000000000000000000 : ℝ) ≤ (2000174064329903/2000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50018824279247149857/50000000000000000000 : ℝ)^1024 ≤ (2000174064329903/2000000000000000 : ℝ)^4429 := by
      have hnat : (50018824279247149857 : ℕ)^1024*2000000000000000^4429 ≤ 2000174064329903^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018824279247149857 50000000000000000000 2000174064329903 2000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000174064329903/2000000000000000 : ℝ)) (X := (50018824279247149857/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015617090895959381/25000000000000000000 : ℝ) ≤ (5000722026371557/5000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (25015617090895959381/25000000000000000000 : ℝ)^1024 ≤ (5000722026371557/5000000000000000 : ℝ)^4429 := by
      have hnat : (25015617090895959381 : ℕ)^1024*5000000000000000^4429 ≤ 5000722026371557^4429*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015617090895959381 25000000000000000000 5000722026371557 5000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000722026371557/5000000000000000 : ℝ)) (X := (25015617090895959381/25000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(801797087797619/12500000000000000000 : ℝ) ≤ ((11852273540786879783/11855000000000000000 : ℝ)+2*(573731093599/474200000000000 : ℝ)*(1073/10000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (11852273540786879783/11855000000000000000 : ℝ)+2*(573731093599/474200000000000 : ℝ)*(1073/10000 : ℝ)=(2500074147638979/2500000000000000 : ℝ) by norm_num, show 1+2*(801797087797619/12500000000000000000 : ℝ)=(6250801797087797619/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15617090895959381/50000000000000000000 : ℝ)+(801797087797619/12500000000000000000 : ℝ) ≤ ((11852273540786879783/11855000000000000000 : ℝ)+(573731093599/474200000000000 : ℝ)*((967/6250 : ℝ)+(1073/10000 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (11852273540786879783/11855000000000000000 : ℝ)+(573731093599/474200000000000 : ℝ)*((967/6250 : ℝ)+(1073/10000 : ℝ))=(2000174064329903/2000000000000000 : ℝ) by norm_num, show 1+(15617090895959381/50000000000000000000 : ℝ)+(801797087797619/12500000000000000000 : ℝ)=(50018824279247149857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15617090895959381/50000000000000000000 : ℝ) ≤ ((11852273540786879783/11855000000000000000 : ℝ)+2*(573731093599/474200000000000 : ℝ)*(967/6250 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (11852273540786879783/11855000000000000000 : ℝ)+2*(573731093599/474200000000000 : ℝ)*(967/6250 : ℝ)=(5000722026371557/5000000000000000 : ℝ) by norm_num, show 1+2*(15617090895959381/50000000000000000000 : ℝ)=(25015617090895959381/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11852273540786879783/11855000000000000000 : ℝ)*(X 1 0+X 2 0)+(573731093599/474200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (1073/10000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (11852273540786879783/11855000000000000000 : ℝ)) (alpha := (573731093599/474200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11852273540786879783/11855000000000000000 : ℝ)*(X 0 1+X 2 1)+(573731093599/474200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (1073/10000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (11852273540786879783/11855000000000000000 : ℝ)) (alpha := (573731093599/474200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11852273540786879783/11855000000000000000 : ℝ)*(X 0 2+X 1 2)+(573731093599/474200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (1073/10000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (11852273540786879783/11855000000000000000 : ℝ)) (alpha := (573731093599/474200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-214319581/1250000000 : ℝ)*X 0 0+(2703858279/5000000000 : ℝ)*X 0 1+(5407714951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317483209/2500000000 : ℝ)*X 1 0+(-1905293261/10000000000 : ℝ)*X 1 1+(54077153/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317483109/2500000000 : ℝ)*X 2 0+(1081543167/2000000000 : ℝ)*X 2 1+(-119080817/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((899296169/2000000000 : ℝ)*X 0 0+(4195850137/10000000000 : ℝ)*X 0 1+(4195850431/10000000000 : ℝ)*X 0 2+(899296169/2000000000 : ℝ)*X 1 0+(4195850137/10000000000 : ℝ)*X 1 1+(4195850431/10000000000 : ℝ)*X 1 2+(899296169/2000000000 : ℝ)*X 2 0+(4195850137/10000000000 : ℝ)*X 2 1+(4195850431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2164125317/10000000000 : ℝ)*X 0 0+(5241862041/10000000000 : ℝ)*X 0 1+(1048372357/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5385812871/10000000000 : ℝ)*X 1 0+(-246620789/1250000000 : ℝ)*X 1 1+(5241861597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5385812929/10000000000 : ℝ)*X 2 0+(5241861477/10000000000 : ℝ)*X 2 1+(-986483197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4083724579/10000000000 : ℝ)*X 0 0+(2201043929/5000000000 : ℝ)*X 0 1+(550260973/1250000000 : ℝ)*X 0 2+(4083724579/10000000000 : ℝ)*X 1 0+(2201043929/5000000000 : ℝ)*X 1 1+(550260973/1250000000 : ℝ)*X 1 2+(4083724579/10000000000 : ℝ)*X 2 0+(2201043929/5000000000 : ℝ)*X 2 1+(550260973/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-517347337/2500000000 : ℝ)*X 0 0+(5126187699/10000000000 : ℝ)*X 0 1+(5428296741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2627772523/5000000000 : ℝ)*X 1 0+(-1896637181/10000000000 : ℝ)*X 1 1+(1357074079/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((328471537/625000000 : ℝ)*X 2 0+(5428296503/10000000000 : ℝ)*X 2 1+(-1896637541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4546543193/10000000000 : ℝ)*X 0 0+(4170226619/10000000000 : ℝ)*X 0 1+(4170227087/10000000000 : ℝ)*X 0 2+(4546543193/10000000000 : ℝ)*X 1 0+(4170226619/10000000000 : ℝ)*X 1 1+(4170227087/10000000000 : ℝ)*X 1 2+(4546543193/10000000000 : ℝ)*X 2 0+(4170226619/10000000000 : ℝ)*X 2 1+(4170227087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-904752033/5000000000 : ℝ)*X 0 0+(1379875643/2500000000 : ℝ)*X 0 1+(1306721909/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((337267109/625000000 : ℝ)*X 1 0+(-494722443/2500000000 : ℝ)*X 1 1+(2613443849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((539627361/1000000000 : ℝ)*X 2 0+(2613443843/5000000000 : ℝ)*X 2 1+(-123680623/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2022800581/5000000000 : ℝ)*X 0 0+(4420685991/10000000000 : ℝ)*X 0 1+(1105171633/2500000000 : ℝ)*X 0 2+(2022800581/5000000000 : ℝ)*X 1 0+(4420685991/10000000000 : ℝ)*X 1 1+(1105171633/2500000000 : ℝ)*X 1 2+(2022800581/5000000000 : ℝ)*X 2 0+(4420685991/10000000000 : ℝ)*X 2 1+(1105171633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6369/10000 : ℝ) ≤ (-47188234567782888138387060958407/74093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27941889/20000000000000 : ℝ)*(upper0) + (67003821/50000000000000 : ℝ)*(upper1) + (9202891/20000000000000 : ℝ)*(upper3) + (7983017/50000000000000 : ℝ)*(upper5) + (539019052368643/25000000000000 : ℝ)*(major0) + (539019052368643/25000000000000 : ℝ)*(major1) + (539019052368643/25000000000000 : ℝ)*(major2) + (1493585259/100000000000000 : ℝ)*(sp2) + (312501937/12500000000000 : ℝ)*(sp3) + (1492045654431643/50000000000000 : ℝ)*(sp4) + (1492046509749723/50000000000000 : ℝ)*(sp5) + (746022881478547/25000000000000 : ℝ)*(sp6) + (1349285966018883/100000000000000 : ℝ)*(sp7) + (2672869/156250000000 : ℝ)*(sp8) + (1349288466034379/100000000000000 : ℝ)*(f.failure) + (1492046509749723/50000000000000 : ℝ)*(f.sum) + (13335544402611/11855000000000000000000000000 : ℝ)*base66 + (959795278777730531/296375000000000000000000000000000 : ℝ)*base68 + (5877719420871519469/296375000000000000000000000000000 : ℝ)*base69 + (3242535272999644469/296375000000000000000000000000000 : ℝ)*base71 + (3246204473207/1481875000000000000000000000 : ℝ)*base74 + (4362503658342519469/296375000000000000000000000000000 : ℝ)*base75 + (1948464779398394469/296375000000000000000000000000000 : ℝ)*base77 + (2388267332706644469/296375000000000000000000000000000 : ℝ)*base79 + (13660540528063/5927500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3685697/1000000000000000000000 : ℝ)*base90 + (3685697/1000000000000000000000 : ℝ)*base92 + (3685697/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58417/100000 : ℝ) ≤ (86570619569637064989240772254903/148187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24428209/50000000000000 : ℝ)*(upper0) + (4074459/50000000000000 : ℝ)*(lower1) + (29564841/100000000000000 : ℝ)*(upper3) + (1114637483730453/50000000000000 : ℝ)*(major0) + (1114637483730453/50000000000000 : ℝ)*(major1) + (1114637483730453/50000000000000 : ℝ)*(major2) + (760991555744339/25000000000000 : ℝ)*(sp0) + (380497187022581/12500000000000 : ℝ)*(sp1) + (1521983494441397/50000000000000 : ℝ)*(sp2) + (1395093284354859/100000000000000 : ℝ)*(sp3) + (2430806969/100000000000000 : ℝ)*(sp5) + (6469052411/50000000000000 : ℝ)*(sp6) + (175337469/5000000000000 : ℝ)*(sp7) + (6852005131/50000000000000 : ℝ)*(sp8) + (1395096791104239/100000000000000 : ℝ)*(f.failure) + (3043979926987617/100000000000000 : ℝ)*(f.sum) + (8878221307471/5927500000000000000000000000 : ℝ)*base65 + (607291402813943301/592750000000000000000000000000000 : ℝ)*base68 + (5567709973836556699/592750000000000000000000000000000 : ℝ)*base69 + (387804794310306699/592750000000000000000000000000000 : ℝ)*base71 + (14049862772531/5927500000000000000000000000 : ℝ)*base73 + (5180182948750306699/592750000000000000000000000000000 : ℝ)*base75 + (4804922019499056699/592750000000000000000000000000000 : ℝ)*base77 + (7828633358796556699/592750000000000000000000000000000 : ℝ)*base79 + (35955847821067/2963750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (805677/1000000000000000000000 : ℝ)*base90 + (805677/1000000000000000000000 : ℝ)*base92 + (805677/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79821/100000 : ℝ) ≤ (7393014058796582674986516587319/9261718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (4214339/10000000000000 : ℝ)*(upper0) + (37569227/25000000000000 : ℝ)*(upper2) + (4766963/20000000000000 : ℝ)*(lower3) + (57013717/50000000000000 : ℝ)*(lower5) + (75878006789771/3125000000000 : ℝ)*(major0) + (75878006789771/3125000000000 : ℝ)*(major1) + (75878006789771/3125000000000 : ℝ)*(major2) + (7003227863/25000000000000 : ℝ)*(sp3) + (4947318581/100000000000000 : ℝ)*(sp4) + (3310057880253219/100000000000000 : ℝ)*(sp8) + (331006404934353/10000000000000 : ℝ)*(sp9) + (331006404934353/10000000000000 : ℝ)*(sp10) + (60779703574841/4000000000000 : ℝ)*(sp11) + (1221771731/100000000000000 : ℝ)*(sp12) + (1519520602282477/100000000000000 : ℝ)*(f.failure) + (331006404934353/10000000000000 : ℝ)*(f.sum) + (7537455973557/5927500000000000000000000000 : ℝ)*base65 + (4041651599013909/18523437500000000000000000000000 : ℝ)*base67 + (28055685454139767/9261718750000000000000000000000 : ℝ)*base69 + (101753530683763909/18523437500000000000000000000000 : ℝ)*base71 + (41563054016731/11855000000000000000000000000 : ℝ)*base74 + (61190121488514767/9261718750000000000000000000000 : ℝ)*base75 + (72152385152670159/18523437500000000000000000000000 : ℝ)*base77 + (171262973596857659/18523437500000000000000000000000 : ℝ)*base79 + (39878882783471/11855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5172711/1000000000000000000000 : ℝ)*base90 + (5172711/1000000000000000000000 : ℝ)*base92 + (5172711/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21427/25000 : ℝ) ≤ (-254008424838507463844005256552523/296375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50441971/100000000000000 : ℝ)*(lower0) + (41838879/50000000000000 : ℝ)*(lower1) + (1648689/20000000000000 : ℝ)*(lower3) + (89887421/100000000000000 : ℝ)*(lower4) + (1233049531474927/50000000000000 : ℝ)*(major0) + (1233049531474927/50000000000000 : ℝ)*(major1) + (1233049531474927/50000000000000 : ℝ)*(major2) + (144908259/400000000000 : ℝ)*(sp5) + (78379297919/100000000000000 : ℝ)*(sp6) + (6354986643/50000000000000 : ℝ)*(sp7) + (3417463420557187/100000000000000 : ℝ)*(sp12) + (3417427193492437/100000000000000 : ℝ)*(sp13) + (854346260314817/25000000000000 : ℝ)*(sp14) + (385822588673279/25000000000000 : ℝ)*(sp15) + (1543303064666403/100000000000000 : ℝ)*(f.failure) + (3417463420557187/100000000000000 : ℝ)*(f.sum) + (26031881545653/11855000000000000000000000000 : ℝ)*base65 + (2458793115967525841/592750000000000000000000000000000 : ℝ)*base67 + (5279922984777525841/592750000000000000000000000000000 : ℝ)*base69 + (3725627629673525841/592750000000000000000000000000000 : ℝ)*base71 + (9845710335627/11855000000000000000000000000 : ℝ)*base74 + (1066951104253474159/592750000000000000000000000000000 : ℝ)*base76 + (2170701614057775841/592750000000000000000000000000000 : ℝ)*base77 + (170263706691724159/592750000000000000000000000000000 : ℝ)*base80 + (70187970272043/11855000000000000000000000000 : ℝ)*base81 + (557129/1000000000000000000000 : ℝ)*base90 + (557129/1000000000000000000000 : ℝ)*base92 + (557129/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1467_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6369/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58417/100000 : ℝ) else (79821/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21427/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1467_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1467_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6369/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58417/100000 : ℝ) else (79821/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21427/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1467_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1467_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1467_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6369/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58417/100000 : ℝ) else (79821/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21427/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1467_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
