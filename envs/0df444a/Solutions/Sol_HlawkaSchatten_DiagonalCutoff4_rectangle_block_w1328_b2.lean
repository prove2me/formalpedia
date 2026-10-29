-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1328_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:55:35.742459+00:00
-- url     : https://prove2.me/submissions/1a0d9821-054d-4fb0-a5b6-a188d16d0bb7

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
theorem support_rectangle_w1328_s6_0 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028061407/5000000000 : ℝ)*x 0 + (1353361463/2500000000 : ℝ)*x 1 + (2622077189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028061407/5000000000 : ℝ)^67 ≤ (12518002355731/100000000000000 : ℝ)^51 := by
    have hnat : (1028061407 : ℕ)^67*100000000000000^51 ≤ 12518002355731^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028061407 5000000000 12518002355731 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353361463/2500000000 : ℝ)^67 ≤ (44653729113257/100000000000000 : ℝ)^51 := by
    have hnat : (1353361463 : ℕ)^67*100000000000000^51 ≤ 44653729113257^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353361463 2500000000 44653729113257 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622077189/5000000000 : ℝ)^67 ≤ (42828268510213/100000000000000 : ℝ)^51 := by
    have hnat : (2622077189 : ℕ)^67*100000000000000^51 ≤ 42828268510213^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622077189 5000000000 42828268510213 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028061407/5000000000 : ℝ), (1353361463/2500000000 : ℝ), (2622077189/5000000000 : ℝ)] ![(12518002355731/100000000000000 : ℝ), (44653729113257/100000000000000 : ℝ), (42828268510213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028061407/5000000000 : ℝ)|^67 ≤ (12518002355731/100000000000000 : ℝ)^51
        have hw : |(-1028061407/5000000000 : ℝ)|=(1028061407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353361463/2500000000 : ℝ)|^67 ≤ (44653729113257/100000000000000 : ℝ)^51
        have hw : |(1353361463/2500000000 : ℝ)|=(1353361463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622077189/5000000000 : ℝ)|^67 ≤ (42828268510213/100000000000000 : ℝ)^51
        have hw : |(2622077189/5000000000 : ℝ)|=(2622077189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s6_1 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5349239013/10000000000 : ℝ)*x 0 + (-2142389659/10000000000 : ℝ)*x 1 + (2622077359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349239013/10000000000 : ℝ)^67 ≤ (4395925047451/10000000000000 : ℝ)^51 := by
    have hnat : (5349239013 : ℕ)^67*10000000000000^51 ≤ 4395925047451^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349239013 10000000000 4395925047451 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142389659/10000000000 : ℝ)^67 ≤ (13212477350783/100000000000000 : ℝ)^51 := by
    have hnat : (2142389659 : ℕ)^67*100000000000000^51 ≤ 13212477350783^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142389659 10000000000 13212477350783 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622077359/5000000000 : ℝ)^67 ≤ (42828272158077/100000000000000 : ℝ)^51 := by
    have hnat : (2622077359 : ℕ)^67*100000000000000^51 ≤ 42828272158077^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622077359 5000000000 42828272158077 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349239013/10000000000 : ℝ), (-2142389659/10000000000 : ℝ), (2622077359/5000000000 : ℝ)] ![(4395925047451/10000000000000 : ℝ), (13212477350783/100000000000000 : ℝ), (42828272158077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349239013/10000000000 : ℝ)|^67 ≤ (4395925047451/10000000000000 : ℝ)^51
        have hw : |(5349239013/10000000000 : ℝ)|=(5349239013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142389659/10000000000 : ℝ)|^67 ≤ (13212477350783/100000000000000 : ℝ)^51
        have hw : |(-2142389659/10000000000 : ℝ)|=(2142389659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622077359/5000000000 : ℝ)|^67 ≤ (42828272158077/100000000000000 : ℝ)^51
        have hw : |(2622077359/5000000000 : ℝ)|=(2622077359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s6_2 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1069847901/2000000000 : ℝ)*x 0 + (655519237/1250000000 : ℝ)*x 1 + (-2142390091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069847901/2000000000 : ℝ)^67 ≤ (21979627893071/50000000000000 : ℝ)^51 := by
    have hnat : (1069847901 : ℕ)^67*50000000000000^51 ≤ 21979627893071^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069847901 2000000000 21979627893071 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655519237/1250000000 : ℝ)^67 ≤ (4282826333883/10000000000000 : ℝ)^51 := by
    have hnat : (655519237 : ℕ)^67*10000000000000^51 ≤ 4282826333883^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655519237 1250000000 4282826333883 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142390091/10000000000 : ℝ)^67 ≤ (13212480850833/100000000000000 : ℝ)^51 := by
    have hnat : (2142390091 : ℕ)^67*100000000000000^51 ≤ 13212480850833^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142390091 10000000000 13212480850833 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069847901/2000000000 : ℝ), (655519237/1250000000 : ℝ), (-2142390091/10000000000 : ℝ)] ![(21979627893071/50000000000000 : ℝ), (4282826333883/10000000000000 : ℝ), (13212480850833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069847901/2000000000 : ℝ)|^67 ≤ (21979627893071/50000000000000 : ℝ)^51
        have hw : |(1069847901/2000000000 : ℝ)|=(1069847901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655519237/1250000000 : ℝ)|^67 ≤ (4282826333883/10000000000000 : ℝ)^51
        have hw : |(655519237/1250000000 : ℝ)|=(655519237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142390091/10000000000 : ℝ)|^67 ≤ (13212480850833/100000000000000 : ℝ)^51
        have hw : |(-2142390091/10000000000 : ℝ)|=(2142390091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s6_3 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1082572773/2500000000 : ℝ)*x 0 + (83146127/200000000 : ℝ)*x 1 + (4510031929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082572773/2500000000 : ℝ)^67 ≤ (6660598168901/20000000000000 : ℝ)^51 := by
    have hnat : (1082572773 : ℕ)^67*20000000000000^51 ≤ 6660598168901^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082572773 2500000000 6660598168901 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83146127/200000000 : ℝ)^67 ≤ (31566297516103/100000000000000 : ℝ)^51 := by
    have hnat : (83146127 : ℕ)^67*100000000000000^51 ≤ 31566297516103^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83146127 200000000 31566297516103 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510031929/10000000000 : ℝ)^67 ≤ (35130711625069/100000000000000 : ℝ)^51 := by
    have hnat : (4510031929 : ℕ)^67*100000000000000^51 ≤ 35130711625069^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510031929 10000000000 35130711625069 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082572773/2500000000 : ℝ), (83146127/200000000 : ℝ), (4510031929/10000000000 : ℝ)] ![(6660598168901/20000000000000 : ℝ), (31566297516103/100000000000000 : ℝ), (35130711625069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082572773/2500000000 : ℝ)|^67 ≤ (6660598168901/20000000000000 : ℝ)^51
        have hw : |(1082572773/2500000000 : ℝ)|=(1082572773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(83146127/200000000 : ℝ)|^67 ≤ (31566297516103/100000000000000 : ℝ)^51
        have hw : |(83146127/200000000 : ℝ)|=(83146127/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510031929/10000000000 : ℝ)|^67 ≤ (35130711625069/100000000000000 : ℝ)^51
        have hw : |(4510031929/10000000000 : ℝ)|=(4510031929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s6_4 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-411227079/2000000000 : ℝ)*x 0 + (2622379953/5000000000 : ℝ)*x 1 + (169151157/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411227079/2000000000 : ℝ)^67 ≤ (6259051490399/50000000000000 : ℝ)^51 := by
    have hnat : (411227079 : ℕ)^67*50000000000000^51 ≤ 6259051490399^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411227079 2000000000 6259051490399 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622379953/5000000000 : ℝ)^67 ≤ (10708691336057/25000000000000 : ℝ)^51 := by
    have hnat : (2622379953 : ℕ)^67*25000000000000^51 ≤ 10708691336057^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622379953 5000000000 10708691336057 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169151157/312500000 : ℝ)^67 ≤ (22323565836103/50000000000000 : ℝ)^51 := by
    have hnat : (169151157 : ℕ)^67*50000000000000^51 ≤ 22323565836103^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169151157 312500000 22323565836103 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411227079/2000000000 : ℝ), (2622379953/5000000000 : ℝ), (169151157/312500000 : ℝ)] ![(6259051490399/50000000000000 : ℝ), (10708691336057/25000000000000 : ℝ), (22323565836103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411227079/2000000000 : ℝ)|^67 ≤ (6259051490399/50000000000000 : ℝ)^51
        have hw : |(-411227079/2000000000 : ℝ)|=(411227079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622379953/5000000000 : ℝ)|^67 ≤ (10708691336057/25000000000000 : ℝ)^51
        have hw : |(2622379953/5000000000 : ℝ)|=(2622379953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169151157/312500000 : ℝ)|^67 ≤ (22323565836103/50000000000000 : ℝ)^51
        have hw : |(169151157/312500000 : ℝ)|=(169151157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s6_5 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2652852439/5000000000 : ℝ)*x 0 + (-394741433/2000000000 : ℝ)*x 1 + (169151157/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652852439/5000000000 : ℝ)^67 ≤ (21744928522263/50000000000000 : ℝ)^51 := by
    have hnat : (2652852439 : ℕ)^67*50000000000000^51 ≤ 21744928522263^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652852439 5000000000 21744928522263 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394741433/2000000000 : ℝ)^67 ≤ (11863011266777/100000000000000 : ℝ)^51 := by
    have hnat : (394741433 : ℕ)^67*100000000000000^51 ≤ 11863011266777^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394741433 2000000000 11863011266777 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169151157/312500000 : ℝ)^67 ≤ (22323565836103/50000000000000 : ℝ)^51 := by
    have hnat : (169151157 : ℕ)^67*50000000000000^51 ≤ 22323565836103^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169151157 312500000 22323565836103 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652852439/5000000000 : ℝ), (-394741433/2000000000 : ℝ), (169151157/312500000 : ℝ)] ![(21744928522263/50000000000000 : ℝ), (11863011266777/100000000000000 : ℝ), (22323565836103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652852439/5000000000 : ℝ)|^67 ≤ (21744928522263/50000000000000 : ℝ)^51
        have hw : |(2652852439/5000000000 : ℝ)|=(2652852439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-394741433/2000000000 : ℝ)|^67 ≤ (11863011266777/100000000000000 : ℝ)^51
        have hw : |(-394741433/2000000000 : ℝ)|=(394741433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169151157/312500000 : ℝ)|^67 ≤ (22323565836103/50000000000000 : ℝ)^51
        have hw : |(169151157/312500000 : ℝ)|=(169151157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s6_6 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5305704879/10000000000 : ℝ)*x 0 + (169151157/312500000 : ℝ)*x 1 + (-394741433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305704879/10000000000 : ℝ)^67 ≤ (21744928527647/50000000000000 : ℝ)^51 := by
    have hnat : (5305704879 : ℕ)^67*50000000000000^51 ≤ 21744928527647^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305704879 10000000000 21744928527647 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169151157/312500000 : ℝ)^67 ≤ (22323565836103/50000000000000 : ℝ)^51 := by
    have hnat : (169151157 : ℕ)^67*50000000000000^51 ≤ 22323565836103^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169151157 312500000 22323565836103 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394741433/2000000000 : ℝ)^67 ≤ (11863011266777/100000000000000 : ℝ)^51 := by
    have hnat : (394741433 : ℕ)^67*100000000000000^51 ≤ 11863011266777^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394741433 2000000000 11863011266777 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305704879/10000000000 : ℝ), (169151157/312500000 : ℝ), (-394741433/2000000000 : ℝ)] ![(21744928527647/50000000000000 : ℝ), (22323565836103/50000000000000 : ℝ), (11863011266777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305704879/10000000000 : ℝ)|^67 ≤ (21744928527647/50000000000000 : ℝ)^51
        have hw : |(5305704879/10000000000 : ℝ)|=(5305704879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169151157/312500000 : ℝ)|^67 ≤ (22323565836103/50000000000000 : ℝ)^51
        have hw : |(169151157/312500000 : ℝ)|=(169151157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394741433/2000000000 : ℝ)|^67 ≤ (11863011266777/100000000000000 : ℝ)^51
        have hw : |(-394741433/2000000000 : ℝ)|=(394741433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s6_7 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (216515853/500000000 : ℝ)*x 0 + (4508770349/10000000000 : ℝ)*x 1 + (4158574157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216515853/500000000 : ℝ)^67 ≤ (2081453325737/6250000000000 : ℝ)^51 := by
    have hnat : (216515853 : ℕ)^67*6250000000000^51 ≤ 2081453325737^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216515853 500000000 2081453325737 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508770349/10000000000 : ℝ)^67 ≤ (35117802176407/100000000000000 : ℝ)^51 := by
    have hnat : (4508770349 : ℕ)^67*100000000000000^51 ≤ 35117802176407^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508770349 10000000000 35117802176407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158574157/10000000000 : ℝ)^67 ≤ (31578944593083/100000000000000 : ℝ)^51 := by
    have hnat : (4158574157 : ℕ)^67*100000000000000^51 ≤ 31578944593083^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158574157 10000000000 31578944593083 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216515853/500000000 : ℝ), (4508770349/10000000000 : ℝ), (4158574157/10000000000 : ℝ)] ![(2081453325737/6250000000000 : ℝ), (35117802176407/100000000000000 : ℝ), (31578944593083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216515853/500000000 : ℝ)|^67 ≤ (2081453325737/6250000000000 : ℝ)^51
        have hw : |(216515853/500000000 : ℝ)|=(216515853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508770349/10000000000 : ℝ)|^67 ≤ (35117802176407/100000000000000 : ℝ)^51
        have hw : |(4508770349/10000000000 : ℝ)|=(4508770349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158574157/10000000000 : ℝ)|^67 ≤ (31578944593083/100000000000000 : ℝ)^51
        have hw : |(4158574157/10000000000 : ℝ)|=(4158574157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1328_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2223/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11107/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (252527410449487/2500000000000000000 : ℝ) := by
    have hpowers : (11107/100000 : ℝ)^4287 ≤ (252527410449487/2500000000000000000 : ℝ)^1024 := by
      have hnat : (11107 : ℕ)^4287*2500000000000000000^1024 ≤ 252527410449487^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11107 100000 252527410449487 2500000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11107/100000 : ℝ)) (X := (252527410449487/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14707/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (32720512829583131/100000000000000000000 : ℝ) := by
    have hpowers : (14707/100000 : ℝ)^4287 ≤ (32720512829583131/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14707 : ℕ)^4287*100000000000000000000^1024 ≤ 32720512829583131^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14707 100000 32720512829583131 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14707/100000 : ℝ)) (X := (32720512829583131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250252527410449487/1250000000000000000 : ℝ) ≤ (10000482515865733/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (1250252527410449487/1250000000000000000 : ℝ)^1024 ≤ (10000482515865733/10000000000000000 : ℝ)^4287 := by
      have hnat : (1250252527410449487 : ℕ)^1024*10000000000000000^4287 ≤ 10000482515865733^4287*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250252527410449487 1250000000000000000 10000482515865733 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000482515865733/10000000000000000 : ℝ)) (X := (1250252527410449487/1250000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042821609247562611/100000000000000000000 : ℝ) ≤ (10001022677483621/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (100042821609247562611/100000000000000000000 : ℝ)^1024 ≤ (10001022677483621/10000000000000000 : ℝ)^4287 := by
      have hnat : (100042821609247562611 : ℕ)^1024*10000000000000000^4287 ≤ 10001022677483621^4287*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042821609247562611 100000000000000000000 10001022677483621 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001022677483621/10000000000000000 : ℝ)) (X := (100042821609247562611/100000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032720512829583131/50000000000000000000 : ℝ) ≤ (10001562839101509/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50032720512829583131/50000000000000000000 : ℝ)^1024 ≤ (10001562839101509/10000000000000000 : ℝ)^4287 := by
      have hnat : (50032720512829583131 : ℕ)^1024*10000000000000000^4287 ≤ 10001562839101509^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032720512829583131 50000000000000000000 10001562839101509 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001562839101509/10000000000000000 : ℝ)) (X := (50032720512829583131/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(252527410449487/2500000000000000000 : ℝ) ≤ ((2249358619183554673/2250000000000000000 : ℝ)+2*(16880050559/11250000000000 : ℝ)*(11107/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (2249358619183554673/2250000000000000000 : ℝ)+2*(16880050559/11250000000000 : ℝ)*(11107/100000 : ℝ)=(10000482515865733/10000000000000000 : ℝ) by norm_num, show 1+2*(252527410449487/2500000000000000000 : ℝ)=(1250252527410449487/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32720512829583131/100000000000000000000 : ℝ)+(252527410449487/2500000000000000000 : ℝ) ≤ ((2249358619183554673/2250000000000000000 : ℝ)+(16880050559/11250000000000 : ℝ)*((14707/100000 : ℝ)+(11107/100000 : ℝ)))^(4287/1024 : ℝ) := by
    rw [show (2249358619183554673/2250000000000000000 : ℝ)+(16880050559/11250000000000 : ℝ)*((14707/100000 : ℝ)+(11107/100000 : ℝ))=(10001022677483621/10000000000000000 : ℝ) by norm_num, show 1+(32720512829583131/100000000000000000000 : ℝ)+(252527410449487/2500000000000000000 : ℝ)=(100042821609247562611/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32720512829583131/100000000000000000000 : ℝ) ≤ ((2249358619183554673/2250000000000000000 : ℝ)+2*(16880050559/11250000000000 : ℝ)*(14707/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (2249358619183554673/2250000000000000000 : ℝ)+2*(16880050559/11250000000000 : ℝ)*(14707/100000 : ℝ)=(10001562839101509/10000000000000000 : ℝ) by norm_num, show 1+2*(32720512829583131/100000000000000000000 : ℝ)=(50032720512829583131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2249358619183554673/2250000000000000000 : ℝ)*(X 1 0+X 2 0)+(16880050559/11250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (2249358619183554673/2250000000000000000 : ℝ)) (alpha := (16880050559/11250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2249358619183554673/2250000000000000000 : ℝ)*(X 0 1+X 2 1)+(16880050559/11250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (2249358619183554673/2250000000000000000 : ℝ)) (alpha := (16880050559/11250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2249358619183554673/2250000000000000000 : ℝ)*(X 0 2+X 1 2)+(16880050559/11250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (2249358619183554673/2250000000000000000 : ℝ)) (alpha := (16880050559/11250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1028061407/5000000000 : ℝ)*X 0 0+(1353361463/2500000000 : ℝ)*X 0 1+(2622077189/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349239013/10000000000 : ℝ)*X 1 0+(-2142389659/10000000000 : ℝ)*X 1 1+(2622077359/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069847901/2000000000 : ℝ)*X 2 0+(655519237/1250000000 : ℝ)*X 2 1+(-2142390091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1082572773/2500000000 : ℝ)*X 0 0+(83146127/200000000 : ℝ)*X 0 1+(4510031929/10000000000 : ℝ)*X 0 2+(1082572773/2500000000 : ℝ)*X 1 0+(83146127/200000000 : ℝ)*X 1 1+(4510031929/10000000000 : ℝ)*X 1 2+(1082572773/2500000000 : ℝ)*X 2 0+(83146127/200000000 : ℝ)*X 2 1+(4510031929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-411227079/2000000000 : ℝ)*X 0 0+(2622379953/5000000000 : ℝ)*X 0 1+(169151157/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652852439/5000000000 : ℝ)*X 1 0+(-394741433/2000000000 : ℝ)*X 1 1+(169151157/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305704879/10000000000 : ℝ)*X 2 0+(169151157/312500000 : ℝ)*X 2 1+(-394741433/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216515853/500000000 : ℝ)*X 0 0+(4508770349/10000000000 : ℝ)*X 0 1+(4158574157/10000000000 : ℝ)*X 0 2+(216515853/500000000 : ℝ)*X 1 0+(4508770349/10000000000 : ℝ)*X 1 1+(4158574157/10000000000 : ℝ)*X 1 2+(216515853/500000000 : ℝ)*X 2 0+(4508770349/10000000000 : ℝ)*X 2 1+(4158574157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33578121582663721355088889/3750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (380592137/50000000000000 : ℝ)*(base19) + (1522635797/100000000000000 : ℝ)*(base23) + (70372553/50000000000000 : ℝ)*(upper3) + (8180201/6250000000000 : ℝ)*(lower4) + (437105574560269/10000000000000 : ℝ)*(major0) + (437105574560269/10000000000000 : ℝ)*(major1) + (437105574560269/10000000000000 : ℝ)*(major2) + (5907001134085213/100000000000000 : ℝ)*(sp0) + (1476756349073979/25000000000000 : ℝ)*(sp1) + (738377671915273/12500000000000 : ℝ)*(sp2) + (1417536793417767/50000000000000 : ℝ)*(sp3) + (25023394977/100000000000000 : ℝ)*(sp4) + (3259522209/100000000000000 : ℝ)*(sp6) + (11448417459/100000000000000 : ℝ)*(sp7) + (2835085035252993/100000000000000 : ℝ)*(f.failure) + (590702615748019/10000000000000 : ℝ)*(f.sum) + (506123946991/225000000000000000000000000 : ℝ)*base66 + (135116214966787037/22500000000000000000000000000000 : ℝ)*base67 + (128261131371787037/22500000000000000000000000000000 : ℝ)*base69 + (191477773409287037/22500000000000000000000000000000 : ℝ)*base71 + (87858485909/225000000000000000000000000 : ℝ)*base73 + (237267090036787037/22500000000000000000000000000000 : ℝ)*base75 + (40816294641787037/22500000000000000000000000000000 : ℝ)*base77 + (283537099521787037/22500000000000000000000000000000 : ℝ)*base79 + (88742942629/56250000000000000000000000 : ℝ)*base82 + (5366837/2500000000000000000000 : ℝ)*base89 + (5366837/2500000000000000000000 : ℝ)*base91 + (5366837/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1273038677581091247881/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445102831/25000000000000 : ℝ)*(base19) + (1935691449/100000000000000 : ℝ)*(base23) + (206913873/100000000000000 : ℝ)*(upper3) + (34917783/50000000000000 : ℝ)*(lower4) + (104321209/50000000000000 : ℝ)*(upper5) + (2201297625306571/50000000000000 : ℝ)*(major0) + (2201297625306571/50000000000000 : ℝ)*(major1) + (2201297625306571/50000000000000 : ℝ)*(major2) + (7230038921/20000000000000 : ℝ)*(sp1) + (4862028241/12500000000000 : ℝ)*(sp2) + (2974824235828127/50000000000000 : ℝ)*(sp4) + (237984421642013/4000000000000 : ℝ)*(sp5) + (5949607639738877/100000000000000 : ℝ)*(sp6) + (571108338018609/20000000000000 : ℝ)*(sp7) + (571108338018609/20000000000000 : ℝ)*(f.failure) + (2974824235828127/50000000000000 : ℝ)*(f.sum) + (3678229924247/562500000000000000000000000 : ℝ)*base66 + (20184410460043717/112500000000000000000000000000000 : ℝ)*base68 + (177573185310043717/112500000000000000000000000000000 : ℝ)*base70 + (1059187507635043717/112500000000000000000000000000000 : ℝ)*base72 + (1788966490369/1125000000000000000000000000 : ℝ)*base74 + (1039251441614956283/112500000000000000000000000000000 : ℝ)*base75 + (488401157714956283/112500000000000000000000000000000 : ℝ)*base77 + (121357980689956283/112500000000000000000000000000000 : ℝ)*base79 + (861958958311/281250000000000000000000000 : ℝ)*base82 + (3046181/500000000000000000000 : ℝ)*base89 + (3046181/500000000000000000000 : ℝ)*base91 + (3046181/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1328_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1328_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1328_s7_0 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056129647/10000000000 : ℝ)*x 0 + (5413378083/10000000000 : ℝ)*x 1 + (5244217733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056129647/10000000000 : ℝ)^67 ≤ (12518057007251/100000000000000 : ℝ)^51 := by
    have hnat : (2056129647 : ℕ)^67*100000000000000^51 ≤ 12518057007251^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056129647 10000000000 12518057007251 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413378083/10000000000 : ℝ)^67 ≤ (44652994736729/100000000000000 : ℝ)^51 := by
    have hnat : (5413378083 : ℕ)^67*100000000000000^51 ≤ 44652994736729^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413378083 10000000000 44652994736729 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244217733/10000000000 : ℝ)^67 ≤ (4282894824797/10000000000000 : ℝ)^51 := by
    have hnat : (5244217733 : ℕ)^67*10000000000000^51 ≤ 4282894824797^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244217733 10000000000 4282894824797 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056129647/10000000000 : ℝ), (5413378083/10000000000 : ℝ), (5244217733/10000000000 : ℝ)] ![(12518057007251/100000000000000 : ℝ), (44652994736729/100000000000000 : ℝ), (4282894824797/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056129647/10000000000 : ℝ)|^67 ≤ (12518057007251/100000000000000 : ℝ)^51
        have hw : |(-2056129647/10000000000 : ℝ)|=(2056129647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413378083/10000000000 : ℝ)|^67 ≤ (44652994736729/100000000000000 : ℝ)^51
        have hw : |(5413378083/10000000000 : ℝ)|=(5413378083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244217733/10000000000 : ℝ)|^67 ≤ (4282894824797/10000000000000 : ℝ)^51
        have hw : |(5244217733/10000000000 : ℝ)|=(5244217733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s7_1 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5349222467/10000000000 : ℝ)*x 0 + (-267791039/1250000000 : ℝ)*x 1 + (5244217693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349222467/10000000000 : ℝ)^67 ≤ (4395907184397/10000000000000 : ℝ)^51 := by
    have hnat : (5349222467 : ℕ)^67*10000000000000^51 ≤ 4395907184397^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349222467 10000000000 4395907184397 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267791039/1250000000 : ℝ)^67 ≤ (2642396064341/20000000000000 : ℝ)^51 := by
    have hnat : (267791039 : ℕ)^67*20000000000000^51 ≤ 2642396064341^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267791039 1250000000 2642396064341 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244217693/10000000000 : ℝ)^67 ≤ (5353618477351/12500000000000 : ℝ)^51 := by
    have hnat : (5244217693 : ℕ)^67*12500000000000^51 ≤ 5353618477351^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244217693 10000000000 5353618477351 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349222467/10000000000 : ℝ), (-267791039/1250000000 : ℝ), (5244217693/10000000000 : ℝ)] ![(4395907184397/10000000000000 : ℝ), (2642396064341/20000000000000 : ℝ), (5353618477351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349222467/10000000000 : ℝ)|^67 ≤ (4395907184397/10000000000000 : ℝ)^51
        have hw : |(5349222467/10000000000 : ℝ)|=(5349222467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267791039/1250000000 : ℝ)|^67 ≤ (2642396064341/20000000000000 : ℝ)^51
        have hw : |(-267791039/1250000000 : ℝ)|=(267791039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244217693/10000000000 : ℝ)|^67 ≤ (5353618477351/12500000000000 : ℝ)^51
        have hw : |(5244217693/10000000000 : ℝ)|=(5244217693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s7_2 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5349222369/10000000000 : ℝ)*x 0 + (1311054421/2500000000 : ℝ)*x 1 + (-428465691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349222369/10000000000 : ℝ)^67 ≤ (43959070785963/100000000000000 : ℝ)^51 := by
    have hnat : (5349222369 : ℕ)^67*100000000000000^51 ≤ 43959070785963^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349222369 10000000000 43959070785963 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311054421/2500000000 : ℝ)^67 ≤ (21414473861123/50000000000000 : ℝ)^51 := by
    have hnat : (1311054421 : ℕ)^67*50000000000000^51 ≤ 21414473861123^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311054421 2500000000 21414473861123 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428465691/2000000000 : ℝ)^67 ≤ (528479259211/4000000000000 : ℝ)^51 := by
    have hnat : (428465691 : ℕ)^67*4000000000000^51 ≤ 528479259211^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428465691 2000000000 528479259211 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349222369/10000000000 : ℝ), (1311054421/2500000000 : ℝ), (-428465691/2000000000 : ℝ)] ![(43959070785963/100000000000000 : ℝ), (21414473861123/50000000000000 : ℝ), (528479259211/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349222369/10000000000 : ℝ)|^67 ≤ (43959070785963/100000000000000 : ℝ)^51
        have hw : |(5349222369/10000000000 : ℝ)|=(5349222369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311054421/2500000000 : ℝ)|^67 ≤ (21414473861123/50000000000000 : ℝ)^51
        have hw : |(1311054421/2500000000 : ℝ)|=(1311054421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428465691/2000000000 : ℝ)|^67 ≤ (528479259211/4000000000000 : ℝ)^51
        have hw : |(-428465691/2000000000 : ℝ)|=(428465691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s7_3 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4330295877/10000000000 : ℝ)*x 0 + (259840119/625000000 : ℝ)*x 1 + (4509895069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330295877/10000000000 : ℝ)^67 ≤ (16651519594821/50000000000000 : ℝ)^51 := by
    have hnat : (4330295877 : ℕ)^67*50000000000000^51 ≤ 16651519594821^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330295877 10000000000 16651519594821 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259840119/625000000 : ℝ)^67 ≤ (6313529936913/20000000000000 : ℝ)^51 := by
    have hnat : (259840119 : ℕ)^67*20000000000000^51 ≤ 6313529936913^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259840119 625000000 6313529936913 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509895069/10000000000 : ℝ)^67 ≤ (35129311114387/100000000000000 : ℝ)^51 := by
    have hnat : (4509895069 : ℕ)^67*100000000000000^51 ≤ 35129311114387^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509895069 10000000000 35129311114387 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330295877/10000000000 : ℝ), (259840119/625000000 : ℝ), (4509895069/10000000000 : ℝ)] ![(16651519594821/50000000000000 : ℝ), (6313529936913/20000000000000 : ℝ), (35129311114387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330295877/10000000000 : ℝ)|^67 ≤ (16651519594821/50000000000000 : ℝ)^51
        have hw : |(4330295877/10000000000 : ℝ)|=(4330295877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259840119/625000000 : ℝ)|^67 ≤ (6313529936913/20000000000000 : ℝ)^51
        have hw : |(259840119/625000000 : ℝ)|=(259840119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509895069/10000000000 : ℝ)|^67 ≤ (35129311114387/100000000000000 : ℝ)^51
        have hw : |(4509895069/10000000000 : ℝ)|=(4509895069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s7_4 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056141981/10000000000 : ℝ)*x 0 + (81950349/156250000 : ℝ)*x 1 + (5412770347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056141981/10000000000 : ℝ)^67 ≤ (1251815565687/10000000000000 : ℝ)^51 := by
    have hnat : (2056141981 : ℕ)^67*10000000000000^51 ≤ 1251815565687^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056141981 10000000000 1251815565687 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81950349/156250000 : ℝ)^67 ≤ (68536696291/160000000000 : ℝ)^51 := by
    have hnat : (81950349 : ℕ)^67*160000000000^51 ≤ 68536696291^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81950349 156250000 68536696291 160000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412770347/10000000000 : ℝ)^67 ≤ (44646409154573/100000000000000 : ℝ)^51 := by
    have hnat : (5412770347 : ℕ)^67*100000000000000^51 ≤ 44646409154573^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412770347 10000000000 44646409154573 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056141981/10000000000 : ℝ), (81950349/156250000 : ℝ), (5412770347/10000000000 : ℝ)] ![(1251815565687/10000000000000 : ℝ), (68536696291/160000000000 : ℝ), (44646409154573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056141981/10000000000 : ℝ)|^67 ≤ (1251815565687/10000000000000 : ℝ)^51
        have hw : |(-2056141981/10000000000 : ℝ)|=(2056141981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81950349/156250000 : ℝ)|^67 ≤ (68536696291/160000000000 : ℝ)^51
        have hw : |(81950349/156250000 : ℝ)|=(81950349/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412770347/10000000000 : ℝ)|^67 ≤ (44646409154573/100000000000000 : ℝ)^51
        have hw : |(5412770347/10000000000 : ℝ)|=(5412770347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s7_5 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5305721909/10000000000 : ℝ)*x 0 + (-246721951/1250000000 : ℝ)*x 1 + (2706385113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305721909/10000000000 : ℝ)^67 ≤ (43490040440537/100000000000000 : ℝ)^51 := by
    have hnat : (5305721909 : ℕ)^67*100000000000000^51 ≤ 43490040440537^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305721909 10000000000 43490040440537 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246721951/1250000000 : ℝ)^67 ≤ (11863551707731/100000000000000 : ℝ)^51 := by
    have hnat : (246721951 : ℕ)^67*100000000000000^51 ≤ 11863551707731^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246721951 1250000000 11863551707731 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706385113/5000000000 : ℝ)^67 ≤ (44646407843409/100000000000000 : ℝ)^51 := by
    have hnat : (2706385113 : ℕ)^67*100000000000000^51 ≤ 44646407843409^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706385113 5000000000 44646407843409 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305721909/10000000000 : ℝ), (-246721951/1250000000 : ℝ), (2706385113/5000000000 : ℝ)] ![(43490040440537/100000000000000 : ℝ), (11863551707731/100000000000000 : ℝ), (44646407843409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305721909/10000000000 : ℝ)|^67 ≤ (43490040440537/100000000000000 : ℝ)^51
        have hw : |(5305721909/10000000000 : ℝ)|=(5305721909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246721951/1250000000 : ℝ)|^67 ≤ (11863551707731/100000000000000 : ℝ)^51
        have hw : |(-246721951/1250000000 : ℝ)|=(246721951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706385113/5000000000 : ℝ)|^67 ≤ (44646407843409/100000000000000 : ℝ)^51
        have hw : |(2706385113/5000000000 : ℝ)|=(2706385113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s7_6 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (530572173/1000000000 : ℝ)*x 0 + (5412770353/10000000000 : ℝ)*x 1 + (-1973775677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530572173/1000000000 : ℝ)^67 ≤ (43490038512999/100000000000000 : ℝ)^51 := by
    have hnat : (530572173 : ℕ)^67*100000000000000^51 ≤ 43490038512999^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530572173 1000000000 43490038512999 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412770353/10000000000 : ℝ)^67 ≤ (44646409219589/100000000000000 : ℝ)^51 := by
    have hnat : (5412770353 : ℕ)^67*100000000000000^51 ≤ 44646409219589^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412770353 10000000000 44646409219589 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973775677/10000000000 : ℝ)^67 ≤ (11863552252573/100000000000000 : ℝ)^51 := by
    have hnat : (1973775677 : ℕ)^67*100000000000000^51 ≤ 11863552252573^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973775677 10000000000 11863552252573 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530572173/1000000000 : ℝ), (5412770353/10000000000 : ℝ), (-1973775677/10000000000 : ℝ)] ![(43490038512999/100000000000000 : ℝ), (44646409219589/100000000000000 : ℝ), (11863552252573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530572173/1000000000 : ℝ)|^67 ≤ (43490038512999/100000000000000 : ℝ)^51
        have hw : |(530572173/1000000000 : ℝ)|=(530572173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412770353/10000000000 : ℝ)|^67 ≤ (44646409219589/100000000000000 : ℝ)^51
        have hw : |(5412770353/10000000000 : ℝ)|=(5412770353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973775677/10000000000 : ℝ)|^67 ≤ (11863552252573/100000000000000 : ℝ)^51
        have hw : |(-1973775677/10000000000 : ℝ)|=(1973775677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s7_7 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4330321559/10000000000 : ℝ)*x 0 + (901727061/2000000000 : ℝ)*x 1 + (4158708113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330321559/10000000000 : ℝ)^67 ≤ (33303298667419/100000000000000 : ℝ)^51 := by
    have hnat : (4330321559 : ℕ)^67*100000000000000^51 ≤ 33303298667419^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330321559 10000000000 33303298667419 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901727061/2000000000 : ℝ)^67 ≤ (702328407407/2000000000000 : ℝ)^51 := by
    have hnat : (901727061 : ℕ)^67*2000000000000^51 ≤ 702328407407^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901727061 2000000000 702328407407 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158708113/10000000000 : ℝ)^67 ≤ (7895070237259/25000000000000 : ℝ)^51 := by
    have hnat : (4158708113 : ℕ)^67*25000000000000^51 ≤ 7895070237259^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158708113 10000000000 7895070237259 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330321559/10000000000 : ℝ), (901727061/2000000000 : ℝ), (4158708113/10000000000 : ℝ)] ![(33303298667419/100000000000000 : ℝ), (702328407407/2000000000000 : ℝ), (7895070237259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330321559/10000000000 : ℝ)|^67 ≤ (33303298667419/100000000000000 : ℝ)^51
        have hw : |(4330321559/10000000000 : ℝ)|=(4330321559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901727061/2000000000 : ℝ)|^67 ≤ (702328407407/2000000000000 : ℝ)^51
        have hw : |(901727061/2000000000 : ℝ)|=(901727061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158708113/10000000000 : ℝ)|^67 ≤ (7895070237259/25000000000000 : ℝ)^51
        have hw : |(4158708113/10000000000 : ℝ)|=(4158708113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1328_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2779/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14697/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2223/20000 : ℝ) ^ (4287/1024 : ℝ) ≤ (10131590363416103/100000000000000000000 : ℝ) := by
    have hpowers : (2223/20000 : ℝ)^4287 ≤ (10131590363416103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2223 : ℕ)^4287*100000000000000000000^1024 ≤ 10131590363416103^1024*20000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2223 20000 10131590363416103 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2223/20000 : ℝ)) (X := (10131590363416103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14699/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (8161515775199571/25000000000000000000 : ℝ) := by
    have hpowers : (14699/100000 : ℝ)^4287 ≤ (8161515775199571/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14699 : ℕ)^4287*25000000000000000000^1024 ≤ 8161515775199571^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14699 100000 8161515775199571 25000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14699/100000 : ℝ)) (X := (8161515775199571/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010131590363416103/50000000000000000000 : ℝ) ≤ (10000483972408409/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50010131590363416103/50000000000000000000 : ℝ)^1024 ≤ (10000483972408409/10000000000000000 : ℝ)^4287 := by
      have hnat : (50010131590363416103 : ℕ)^1024*10000000000000000^4287 ≤ 10000483972408409^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010131590363416103 50000000000000000000 10000483972408409 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000483972408409/10000000000000000 : ℝ)) (X := (50010131590363416103/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042777653464214387/100000000000000000000 : ℝ) ≤ (10001021627890321/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (100042777653464214387/100000000000000000000 : ℝ)^1024 ≤ (10001021627890321/10000000000000000 : ℝ)^4287 := by
      have hnat : (100042777653464214387 : ℕ)^1024*10000000000000000^4287 ≤ 10001021627890321^4287*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042777653464214387 100000000000000000000 10001021627890321 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001021627890321/10000000000000000 : ℝ)) (X := (100042777653464214387/100000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508161515775199571/12500000000000000000 : ℝ) ≤ (10001559283372233/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (12508161515775199571/12500000000000000000 : ℝ)^1024 ≤ (10001559283372233/10000000000000000 : ℝ)^4287 := by
      have hnat : (12508161515775199571 : ℕ)^1024*10000000000000000^4287 ≤ 10001559283372233^4287*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508161515775199571 12500000000000000000 10001559283372233 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001559283372233/10000000000000000 : ℝ)) (X := (12508161515775199571/12500000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10131590363416103/100000000000000000000 : ℝ) ≤ ((2239361404734302131/2240000000000000000 : ℝ)+2*(67206935239/44800000000000 : ℝ)*(2223/20000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (2239361404734302131/2240000000000000000 : ℝ)+2*(67206935239/44800000000000 : ℝ)*(2223/20000 : ℝ)=(10000483972408409/10000000000000000 : ℝ) by norm_num, show 1+2*(10131590363416103/100000000000000000000 : ℝ)=(50010131590363416103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8161515775199571/25000000000000000000 : ℝ)+(10131590363416103/100000000000000000000 : ℝ) ≤ ((2239361404734302131/2240000000000000000 : ℝ)+(67206935239/44800000000000 : ℝ)*((14699/100000 : ℝ)+(2223/20000 : ℝ)))^(4287/1024 : ℝ) := by
    rw [show (2239361404734302131/2240000000000000000 : ℝ)+(67206935239/44800000000000 : ℝ)*((14699/100000 : ℝ)+(2223/20000 : ℝ))=(10001021627890321/10000000000000000 : ℝ) by norm_num, show 1+(8161515775199571/25000000000000000000 : ℝ)+(10131590363416103/100000000000000000000 : ℝ)=(100042777653464214387/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8161515775199571/25000000000000000000 : ℝ) ≤ ((2239361404734302131/2240000000000000000 : ℝ)+2*(67206935239/44800000000000 : ℝ)*(14699/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (2239361404734302131/2240000000000000000 : ℝ)+2*(67206935239/44800000000000 : ℝ)*(14699/100000 : ℝ)=(10001559283372233/10000000000000000 : ℝ) by norm_num, show 1+2*(8161515775199571/25000000000000000000 : ℝ)=(12508161515775199571/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2239361404734302131/2240000000000000000 : ℝ)*(X 1 0+X 2 0)+(67206935239/44800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (2239361404734302131/2240000000000000000 : ℝ)) (alpha := (67206935239/44800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2239361404734302131/2240000000000000000 : ℝ)*(X 0 1+X 2 1)+(67206935239/44800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (2239361404734302131/2240000000000000000 : ℝ)) (alpha := (67206935239/44800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2239361404734302131/2240000000000000000 : ℝ)*(X 0 2+X 1 2)+(67206935239/44800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (2239361404734302131/2240000000000000000 : ℝ)) (alpha := (67206935239/44800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2056129647/10000000000 : ℝ)*X 0 0+(5413378083/10000000000 : ℝ)*X 0 1+(5244217733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349222467/10000000000 : ℝ)*X 1 0+(-267791039/1250000000 : ℝ)*X 1 1+(5244217693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349222369/10000000000 : ℝ)*X 2 0+(1311054421/2500000000 : ℝ)*X 2 1+(-428465691/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330295877/10000000000 : ℝ)*X 0 0+(259840119/625000000 : ℝ)*X 0 1+(4509895069/10000000000 : ℝ)*X 0 2+(4330295877/10000000000 : ℝ)*X 1 0+(259840119/625000000 : ℝ)*X 1 1+(4509895069/10000000000 : ℝ)*X 1 2+(4330295877/10000000000 : ℝ)*X 2 0+(259840119/625000000 : ℝ)*X 2 1+(4509895069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2056141981/10000000000 : ℝ)*X 0 0+(81950349/156250000 : ℝ)*X 0 1+(5412770347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305721909/10000000000 : ℝ)*X 1 0+(-246721951/1250000000 : ℝ)*X 1 1+(2706385113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530572173/1000000000 : ℝ)*X 2 0+(5412770353/10000000000 : ℝ)*X 2 1+(-1973775677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330321559/10000000000 : ℝ)*X 0 0+(901727061/2000000000 : ℝ)*X 0 1+(4158708113/10000000000 : ℝ)*X 0 2+(4330321559/10000000000 : ℝ)*X 1 0+(901727061/2000000000 : ℝ)*X 1 1+(4158708113/10000000000 : ℝ)*X 1 2+(4330321559/10000000000 : ℝ)*X 2 0+(901727061/2000000000 : ℝ)*X 2 1+(4158708113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122720582257689832167889521/11200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1101580437/50000000000000 : ℝ)*(base19) + (202706429/10000000000000 : ℝ)*(base23) + (36263907/100000000000000 : ℝ)*(lower2) + (329102371/100000000000000 : ℝ)*(upper3) + (86081107/100000000000000 : ℝ)*(upper5) + (437447145154701/10000000000000 : ℝ)*(major0) + (437447145154701/10000000000000 : ℝ)*(major1) + (437447145154701/10000000000000 : ℝ)*(major2) + (184737525826857/3125000000000 : ℝ)*(sp0) + (2955819929140603/50000000000000 : ℝ)*(sp1) + (591164003437779/10000000000000 : ℝ)*(sp2) + (177329790148493/6250000000000 : ℝ)*(sp3) + (8246996531/20000000000000 : ℝ)*(sp4) + (23834036213/100000000000000 : ℝ)*(sp7) + (1418650238206051/50000000000000 : ℝ)*(f.failure) + (36947762884013/625000000000 : ℝ)*(f.sum) + (729955289499/224000000000000000000000000 : ℝ)*base65 + (59232240734616833/3200000000000000000000000000000 : ℝ)*base67 + (36099144961816833/3200000000000000000000000000000 : ℝ)*base69 + (50544278955416833/3200000000000000000000000000000 : ℝ)*base71 + (1122076364859/224000000000000000000000000 : ℝ)*base73 + (29425606782616833/3200000000000000000000000000000 : ℝ)*base75 + (18141945169816833/3200000000000000000000000000000 : ℝ)*base77 + (455114053016833/3200000000000000000000000000000 : ℝ)*base79 + (59534807809/44800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (10413759/1250000000000000000000 : ℝ)*base89 + (10413759/1250000000000000000000 : ℝ)*base91 + (10413759/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93341819909249314945651257/28000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1204147421/100000000000000 : ℝ)*(base19) + (1021033737/100000000000000 : ℝ)*(base23) + (369306067/100000000000000 : ℝ)*(lower1) + (20974291/100000000000000 : ℝ)*(upper2) + (16567101/25000000000000 : ℝ)*(upper3) + (33608997/50000000000000 : ℝ)*(upper5) + (1101490671511317/25000000000000 : ℝ)*(major0) + (1101490671511317/25000000000000 : ℝ)*(major1) + (1101490671511317/25000000000000 : ℝ)*(major2) + (663736769/25000000000000 : ℝ)*(sp1) + (5954199438173217/100000000000000 : ℝ)*(sp4) + (18606861184621/312500000000 : ℝ)*(sp5) + (5954198417139479/100000000000000 : ℝ)*(sp6) + (357215727849511/12500000000000 : ℝ)*(sp7) + (357215727849511/12500000000000 : ℝ)*(f.failure) + (5954199438173217/100000000000000 : ℝ)*(f.sum) + (834218856637/560000000000000000000000000 : ℝ)*base66 + (71989645848552361/8000000000000000000000000000000 : ℝ)*base67 + (131140873920552361/8000000000000000000000000000000 : ℝ)*base69 + (47814986552552361/8000000000000000000000000000000 : ℝ)*base71 + (484765353683/560000000000000000000000000 : ℝ)*base73 + (89246393208552361/8000000000000000000000000000000 : ℝ)*base75 + (97444220968552361/8000000000000000000000000000000 : ℝ)*base77 + (156481716448552361/8000000000000000000000000000000 : ℝ)*base79 + (744546810397/560000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5017101/312500000000000000000 : ℝ)*base90 + (5017101/312500000000000000000 : ℝ)*base92 + (5017101/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1328_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2779/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1328_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1328_s8_0 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-411227121/2000000000 : ℝ)*x 0 + (216534541/400000000 : ℝ)*x 1 + (2622113997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411227121/2000000000 : ℝ)^67 ≤ (12518104660417/100000000000000 : ℝ)^51 := by
    have hnat : (411227121 : ℕ)^67*100000000000000^51 ≤ 12518104660417^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411227121 2000000000 12518104660417 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216534541/400000000 : ℝ)^67 ≤ (2232641848991/5000000000000 : ℝ)^51 := by
    have hnat : (216534541 : ℕ)^67*5000000000000^51 ≤ 2232641848991^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216534541 400000000 2232641848991 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622113997/5000000000 : ℝ)^67 ≤ (42829058338799/100000000000000 : ℝ)^51 := by
    have hnat : (2622113997 : ℕ)^67*100000000000000^51 ≤ 42829058338799^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622113997 5000000000 42829058338799 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411227121/2000000000 : ℝ), (216534541/400000000 : ℝ), (2622113997/5000000000 : ℝ)] ![(12518104660417/100000000000000 : ℝ), (2232641848991/5000000000000 : ℝ), (42829058338799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411227121/2000000000 : ℝ)|^67 ≤ (12518104660417/100000000000000 : ℝ)^51
        have hw : |(-411227121/2000000000 : ℝ)|=(411227121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216534541/400000000 : ℝ)|^67 ≤ (2232641848991/5000000000000 : ℝ)^51
        have hw : |(216534541/400000000 : ℝ)|=(216534541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622113997/5000000000 : ℝ)|^67 ≤ (42829058338799/100000000000000 : ℝ)^51
        have hw : |(2622113997/5000000000 : ℝ)|=(2622113997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s8_1 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (668652267/1250000000 : ℝ)*x 0 + (-2142317447/10000000000 : ℝ)*x 1 + (327764391/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668652267/1250000000 : ℝ)^67 ≤ (21979512543271/50000000000000 : ℝ)^51 := by
    have hnat : (668652267 : ℕ)^67*50000000000000^51 ≤ 21979512543271^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668652267 1250000000 21979512543271 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142317447/10000000000 : ℝ)^67 ≤ (825743268419/6250000000000 : ℝ)^51 := by
    have hnat : (2142317447 : ℕ)^67*6250000000000^51 ≤ 825743268419^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142317447 10000000000 825743268419 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327764391/625000000 : ℝ)^67 ≤ (42829082607929/100000000000000 : ℝ)^51 := by
    have hnat : (327764391 : ℕ)^67*100000000000000^51 ≤ 42829082607929^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327764391 625000000 42829082607929 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668652267/1250000000 : ℝ), (-2142317447/10000000000 : ℝ), (327764391/625000000 : ℝ)] ![(21979512543271/50000000000000 : ℝ), (825743268419/6250000000000 : ℝ), (42829082607929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668652267/1250000000 : ℝ)|^67 ≤ (21979512543271/50000000000000 : ℝ)^51
        have hw : |(668652267/1250000000 : ℝ)|=(668652267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142317447/10000000000 : ℝ)|^67 ≤ (825743268419/6250000000000 : ℝ)^51
        have hw : |(-2142317447/10000000000 : ℝ)|=(2142317447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327764391/625000000 : ℝ)|^67 ≤ (42829082607929/100000000000000 : ℝ)^51
        have hw : |(327764391/625000000 : ℝ)|=(327764391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s8_2 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5349216323/10000000000 : ℝ)*x 0 + (5244230043/10000000000 : ℝ)*x 1 + (-133895009/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349216323/10000000000 : ℝ)^67 ≤ (21979502756709/50000000000000 : ℝ)^51 := by
    have hnat : (5349216323 : ℕ)^67*50000000000000^51 ≤ 21979502756709^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349216323 10000000000 21979502756709 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244230043/10000000000 : ℝ)^67 ≤ (535363504033/1250000000000 : ℝ)^51 := by
    have hnat : (5244230043 : ℕ)^67*1250000000000^51 ≤ 535363504033^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244230043 10000000000 535363504033 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133895009/625000000 : ℝ)^67 ≤ (330297853637/2500000000000 : ℝ)^51 := by
    have hnat : (133895009 : ℕ)^67*2500000000000^51 ≤ 330297853637^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133895009 625000000 330297853637 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349216323/10000000000 : ℝ), (5244230043/10000000000 : ℝ), (-133895009/625000000 : ℝ)] ![(21979502756709/50000000000000 : ℝ), (535363504033/1250000000000 : ℝ), (330297853637/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349216323/10000000000 : ℝ)|^67 ≤ (21979502756709/50000000000000 : ℝ)^51
        have hw : |(5349216323/10000000000 : ℝ)|=(5349216323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244230043/10000000000 : ℝ)|^67 ≤ (535363504033/1250000000000 : ℝ)^51
        have hw : |(5244230043/10000000000 : ℝ)|=(5244230043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133895009/625000000 : ℝ)|^67 ≤ (330297853637/2500000000000 : ℝ)^51
        have hw : |(-133895009/625000000 : ℝ)|=(133895009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s8_3 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4330298471/10000000000 : ℝ)*x 0 + (4157465949/10000000000 : ℝ)*x 1 + (4509869069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330298471/10000000000 : ℝ)^67 ≤ (33303065398067/100000000000000 : ℝ)^51 := by
    have hnat : (4330298471 : ℕ)^67*100000000000000^51 ≤ 33303065398067^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330298471 10000000000 33303065398067 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4157465949/10000000000 : ℝ)^67 ≤ (6313577907591/20000000000000 : ℝ)^51 := by
    have hnat : (4157465949 : ℕ)^67*20000000000000^51 ≤ 6313577907591^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157465949 10000000000 6313577907591 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509869069/10000000000 : ℝ)^67 ≤ (35129045053657/100000000000000 : ℝ)^51 := by
    have hnat : (4509869069 : ℕ)^67*100000000000000^51 ≤ 35129045053657^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509869069 10000000000 35129045053657 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330298471/10000000000 : ℝ), (4157465949/10000000000 : ℝ), (4509869069/10000000000 : ℝ)] ![(33303065398067/100000000000000 : ℝ), (6313577907591/20000000000000 : ℝ), (35129045053657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330298471/10000000000 : ℝ)|^67 ≤ (33303065398067/100000000000000 : ℝ)^51
        have hw : |(4330298471/10000000000 : ℝ)|=(4330298471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4157465949/10000000000 : ℝ)|^67 ≤ (6313577907591/20000000000000 : ℝ)^51
        have hw : |(4157465949/10000000000 : ℝ)|=(4157465949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509869069/10000000000 : ℝ)|^67 ≤ (35129045053657/100000000000000 : ℝ)^51
        have hw : |(4509869069/10000000000 : ℝ)|=(4509869069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s8_4 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056145901/10000000000 : ℝ)*x 0 + (524483341/1000000000 : ℝ)*x 1 + (676594561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056145901/10000000000 : ℝ)^67 ≤ (2503637401959/20000000000000 : ℝ)^51 := by
    have hnat : (2056145901 : ℕ)^67*20000000000000^51 ≤ 2503637401959^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056145901 10000000000 2503637401959 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524483341/1000000000 : ℝ)^67 ≤ (21417776999863/50000000000000 : ℝ)^51 := by
    have hnat : (524483341 : ℕ)^67*50000000000000^51 ≤ 21417776999863^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524483341 1000000000 21417776999863 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676594561/1250000000 : ℝ)^67 ≤ (22323129488811/50000000000000 : ℝ)^51 := by
    have hnat : (676594561 : ℕ)^67*50000000000000^51 ≤ 22323129488811^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676594561 1250000000 22323129488811 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056145901/10000000000 : ℝ), (524483341/1000000000 : ℝ), (676594561/1250000000 : ℝ)] ![(2503637401959/20000000000000 : ℝ), (21417776999863/50000000000000 : ℝ), (22323129488811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056145901/10000000000 : ℝ)|^67 ≤ (2503637401959/20000000000000 : ℝ)^51
        have hw : |(-2056145901/10000000000 : ℝ)|=(2056145901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524483341/1000000000 : ℝ)|^67 ≤ (21417776999863/50000000000000 : ℝ)^51
        have hw : |(524483341/1000000000 : ℝ)|=(524483341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676594561/1250000000 : ℝ)|^67 ≤ (22323129488811/50000000000000 : ℝ)^51
        have hw : |(676594561/1250000000 : ℝ)|=(676594561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s8_5 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5305723923/10000000000 : ℝ)*x 0 + (2706378273/5000000000 : ℝ)*x 1 + (-986895817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305723923/10000000000 : ℝ)^67 ≤ (21745031064017/50000000000000 : ℝ)^51 := by
    have hnat : (5305723923 : ℕ)^67*50000000000000^51 ≤ 21745031064017^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305723923 10000000000 21745031064017 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706378273/5000000000 : ℝ)^67 ≤ (22323129803057/50000000000000 : ℝ)^51 := by
    have hnat : (2706378273 : ℕ)^67*50000000000000^51 ≤ 22323129803057^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706378273 5000000000 22323129803057 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986895817/5000000000 : ℝ)^67 ≤ (5931839126697/50000000000000 : ℝ)^51 := by
    have hnat : (986895817 : ℕ)^67*50000000000000^51 ≤ 5931839126697^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986895817 5000000000 5931839126697 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305723923/10000000000 : ℝ), (2706378273/5000000000 : ℝ), (-986895817/5000000000 : ℝ)] ![(21745031064017/50000000000000 : ℝ), (22323129803057/50000000000000 : ℝ), (5931839126697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305723923/10000000000 : ℝ)|^67 ≤ (21745031064017/50000000000000 : ℝ)^51
        have hw : |(5305723923/10000000000 : ℝ)|=(5305723923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706378273/5000000000 : ℝ)|^67 ≤ (22323129803057/50000000000000 : ℝ)^51
        have hw : |(2706378273/5000000000 : ℝ)|=(2706378273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986895817/5000000000 : ℝ)|^67 ≤ (5931839126697/50000000000000 : ℝ)^51
        have hw : |(-986895817/5000000000 : ℝ)|=(986895817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s8_6 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (433032261/1000000000 : ℝ)*x 0 + (450860917/1000000000 : ℝ)*x 1 + (831746771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433032261/1000000000 : ℝ)^67 ≤ (6660661857239/20000000000000 : ℝ)^51 := by
    have hnat : (433032261 : ℕ)^67*20000000000000^51 ≤ 6660661857239^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433032261 1000000000 6660661857239 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450860917/1000000000 : ℝ)^67 ≤ (4389519118949/12500000000000 : ℝ)^51 := by
    have hnat : (450860917 : ℕ)^67*12500000000000^51 ≤ 4389519118949^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450860917 1000000000 4389519118949 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831746771/2000000000 : ℝ)^67 ≤ (31580537754869/100000000000000 : ℝ)^51 := by
    have hnat : (831746771 : ℕ)^67*100000000000000^51 ≤ 31580537754869^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831746771 2000000000 31580537754869 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433032261/1000000000 : ℝ), (450860917/1000000000 : ℝ), (831746771/2000000000 : ℝ)] ![(6660661857239/20000000000000 : ℝ), (4389519118949/12500000000000 : ℝ), (31580537754869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433032261/1000000000 : ℝ)|^67 ≤ (6660661857239/20000000000000 : ℝ)^51
        have hw : |(433032261/1000000000 : ℝ)|=(433032261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450860917/1000000000 : ℝ)|^67 ≤ (4389519118949/12500000000000 : ℝ)^51
        have hw : |(450860917/1000000000 : ℝ)|=(450860917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831746771/2000000000 : ℝ)|^67 ≤ (31580537754869/100000000000000 : ℝ)^51
        have hw : |(831746771/2000000000 : ℝ)|=(831746771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s8_7 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3724151/1250000000 : ℝ)*x 0 + (5897938991/10000000000 : ℝ)*x 1 + (5897901217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3724151/1250000000 : ℝ)^67 ≤ (48048902311/100000000000000 : ℝ)^51 := by
    have hnat : (3724151 : ℕ)^67*100000000000000^51 ≤ 48048902311^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724151 1250000000 48048902311 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5897938991/10000000000 : ℝ)^67 ≤ (49976185792289/100000000000000 : ℝ)^51 := by
    have hnat : (5897938991 : ℕ)^67*100000000000000^51 ≤ 49976185792289^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5897938991 10000000000 49976185792289 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5897901217/10000000000 : ℝ)^67 ≤ (49975765298101/100000000000000 : ℝ)^51 := by
    have hnat : (5897901217 : ℕ)^67*100000000000000^51 ≤ 49975765298101^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5897901217 10000000000 49975765298101 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3724151/1250000000 : ℝ), (5897938991/10000000000 : ℝ), (5897901217/10000000000 : ℝ)] ![(48048902311/100000000000000 : ℝ), (49976185792289/100000000000000 : ℝ), (49975765298101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3724151/1250000000 : ℝ)|^67 ≤ (48048902311/100000000000000 : ℝ)^51
        have hw : |(-3724151/1250000000 : ℝ)|=(3724151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5897938991/10000000000 : ℝ)|^67 ≤ (49976185792289/100000000000000 : ℝ)^51
        have hw : |(5897938991/10000000000 : ℝ)|=(5897938991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5897901217/10000000000 : ℝ)|^67 ≤ (49975765298101/100000000000000 : ℝ)^51
        have hw : |(5897901217/10000000000 : ℝ)|=(5897901217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1328_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2779/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11117/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14697/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2779/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2779/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2779/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2779/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2779/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2779/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2779/25000 : ℝ) ^ (4287/1024 : ℝ) ≤ (10135407027472551/100000000000000000000 : ℝ) := by
    have hpowers : (2779/25000 : ℝ)^4287 ≤ (10135407027472551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2779 : ℕ)^4287*100000000000000000000^1024 ≤ 10135407027472551^1024*25000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2779 25000 10135407027472551 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2779/25000 : ℝ)) (X := (10135407027472551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14697/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (32627470831599221/100000000000000000000 : ℝ) := by
    have hpowers : (14697/100000 : ℝ)^4287 ≤ (32627470831599221/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14697 : ℕ)^4287*100000000000000000000^1024 ≤ 32627470831599221^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14697 100000 32627470831599221 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14697/100000 : ℝ)) (X := (32627470831599221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010135407027472551/50000000000000000000 : ℝ) ≤ (10000484154711241/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50010135407027472551/50000000000000000000 : ℝ)^1024 ≤ (10000484154711241/10000000000000000 : ℝ)^4287 := by
      have hnat : (50010135407027472551 : ℕ)^1024*10000000000000000^4287 ≤ 10000484154711241^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010135407027472551 50000000000000000000 10000484154711241 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000484154711241/10000000000000000 : ℝ)) (X := (50010135407027472551/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010690719464767943/25000000000000000000 : ℝ) ≤ (625063829692037/625000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (25010690719464767943/25000000000000000000 : ℝ)^1024 ≤ (625063829692037/625000000000000 : ℝ)^4287 := by
      have hnat : (25010690719464767943 : ℕ)^1024*625000000000000^4287 ≤ 625063829692037^4287*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010690719464767943 25000000000000000000 625063829692037 625000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625063829692037/625000000000000 : ℝ)) (X := (25010690719464767943/25000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032627470831599221/50000000000000000000 : ℝ) ≤ (10001558395433943/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50032627470831599221/50000000000000000000 : ℝ)^1024 ≤ (10001558395433943/10000000000000000 : ℝ)^4287 := by
      have hnat : (50032627470831599221 : ℕ)^1024*10000000000000000^4287 ≤ 10001558395433943^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032627470831599221 50000000000000000000 10001558395433943 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001558395433943/10000000000000000 : ℝ)) (X := (50032627470831599221/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10135407027472551/100000000000000000000 : ℝ) ≤ ((35799792498147398589/35810000000000000000 : ℝ)+2*(537120361351/358100000000000 : ℝ)*(2779/25000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (35799792498147398589/35810000000000000000 : ℝ)+2*(537120361351/358100000000000 : ℝ)*(2779/25000 : ℝ)=(10000484154711241/10000000000000000 : ℝ) by norm_num, show 1+2*(10135407027472551/100000000000000000000 : ℝ)=(50010135407027472551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32627470831599221/100000000000000000000 : ℝ)+(10135407027472551/100000000000000000000 : ℝ) ≤ ((35799792498147398589/35810000000000000000 : ℝ)+(537120361351/358100000000000 : ℝ)*((14697/100000 : ℝ)+(2779/25000 : ℝ)))^(4287/1024 : ℝ) := by
    rw [show (35799792498147398589/35810000000000000000 : ℝ)+(537120361351/358100000000000 : ℝ)*((14697/100000 : ℝ)+(2779/25000 : ℝ))=(625063829692037/625000000000000 : ℝ) by norm_num, show 1+(32627470831599221/100000000000000000000 : ℝ)+(10135407027472551/100000000000000000000 : ℝ)=(25010690719464767943/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32627470831599221/100000000000000000000 : ℝ) ≤ ((35799792498147398589/35810000000000000000 : ℝ)+2*(537120361351/358100000000000 : ℝ)*(14697/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (35799792498147398589/35810000000000000000 : ℝ)+2*(537120361351/358100000000000 : ℝ)*(14697/100000 : ℝ)=(10001558395433943/10000000000000000 : ℝ) by norm_num, show 1+2*(32627470831599221/100000000000000000000 : ℝ)=(50032627470831599221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35799792498147398589/35810000000000000000 : ℝ)*(X 1 0+X 2 0)+(537120361351/358100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (2779/25000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (35799792498147398589/35810000000000000000 : ℝ)) (alpha := (537120361351/358100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35799792498147398589/35810000000000000000 : ℝ)*(X 0 1+X 2 1)+(537120361351/358100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (2779/25000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (35799792498147398589/35810000000000000000 : ℝ)) (alpha := (537120361351/358100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35799792498147398589/35810000000000000000 : ℝ)*(X 0 2+X 1 2)+(537120361351/358100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (2779/25000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (35799792498147398589/35810000000000000000 : ℝ)) (alpha := (537120361351/358100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-411227121/2000000000 : ℝ)*X 0 0+(216534541/400000000 : ℝ)*X 0 1+(2622113997/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668652267/1250000000 : ℝ)*X 1 0+(-2142317447/10000000000 : ℝ)*X 1 1+(327764391/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349216323/10000000000 : ℝ)*X 2 0+(5244230043/10000000000 : ℝ)*X 2 1+(-133895009/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330298471/10000000000 : ℝ)*X 0 0+(4157465949/10000000000 : ℝ)*X 0 1+(4509869069/10000000000 : ℝ)*X 0 2+(4330298471/10000000000 : ℝ)*X 1 0+(4157465949/10000000000 : ℝ)*X 1 1+(4509869069/10000000000 : ℝ)*X 1 2+(4330298471/10000000000 : ℝ)*X 2 0+(4157465949/10000000000 : ℝ)*X 2 1+(4509869069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2056145901/10000000000 : ℝ)*X 0 0+(524483341/1000000000 : ℝ)*X 0 1+(676594561/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305723923/10000000000 : ℝ)*X 2 0+(2706378273/5000000000 : ℝ)*X 2 1+(-986895817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((433032261/1000000000 : ℝ)*X 0 0+(450860917/1000000000 : ℝ)*X 0 1+(831746771/2000000000 : ℝ)*X 0 2+(433032261/1000000000 : ℝ)*X 1 0+(450860917/1000000000 : ℝ)*X 1 1+(831746771/2000000000 : ℝ)*X 1 2+(433032261/1000000000 : ℝ)*X 2 0+(450860917/1000000000 : ℝ)*X 2 1+(831746771/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-3724151/1250000000 : ℝ)*X 0 0+(5897938991/10000000000 : ℝ)*X 0 1+(5897901217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s8_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15877999795475374077279/4476250000000000000000000000 : ℝ) := by norm_num
    linear_combination (244883581/100000000000000 : ℝ)*(upper2) + (667369871/100000000000000 : ℝ)*(upper3) + (497259697/50000000000000 : ℝ)*(lower4) + (2187560081187041/50000000000000 : ℝ)*(major0) + (2187560081187041/50000000000000 : ℝ)*(major1) + (2187560081187041/50000000000000 : ℝ)*(major2) + (295625006276047/5000000000000 : ℝ)*(sp0) + (5912518973542017/100000000000000 : ℝ)*(sp1) + (29562402347533/500000000000 : ℝ)*(sp2) + (709423532848427/25000000000000 : ℝ)*(sp3) + (5792114327/50000000000000 : ℝ)*(sp4) + (38504035417/100000000000000 : ℝ)*(sp5) + (13550786789/50000000000000 : ℝ)*(sp6) + (907974053/12500000000000 : ℝ)*(sp7) + (1418860616483643/50000000000000 : ℝ)*(f.failure) + (5912518973542017/100000000000000 : ℝ)*(f.sum) + (3896521859441/2238125000000000000000000000 : ℝ)*base66 + (1026347132000414851/1790500000000000000000000000000000 : ℝ)*base68 + (10562327368733414851/1790500000000000000000000000000000 : ℝ)*base70 + (105198769415552414851/1790500000000000000000000000000000 : ℝ)*base72 + (50979431636683/17905000000000000000000000000 : ℝ)*base74 + (9673035539570585149/1790500000000000000000000000000000 : ℝ)*base75 + (444325229848085149/1790500000000000000000000000000000 : ℝ)*base77 + (6044112377350585149/1790500000000000000000000000000000 : ℝ)*base79 + (8345714416431/8952500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4237687/1250000000000000000000 : ℝ)*base89 + (4237687/1250000000000000000000 : ℝ)*base91 + (4237687/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1328_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2779/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1328_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1328_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1328_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1328_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1328_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1328_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
