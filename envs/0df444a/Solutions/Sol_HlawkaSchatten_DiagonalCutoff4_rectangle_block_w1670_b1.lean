-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1670_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:40.158305+00:00
-- url     : https://prove2.me/submissions/9703c7c9-4652-421a-8709-aa3945d85e5b

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
theorem support_rectangle_w1670_s3_0 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156413161/1000000000 : ℝ)*x 0 + (5441726811/10000000000 : ℝ)*x 1 + (518502707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156413161/1000000000 : ℝ)^4999 ≤ (9698620928209/100000000000000 : ℝ)^3975 := by
    have hnat : (156413161 : ℕ)^4999*100000000000000^3975 ≤ 9698620928209^3975*1000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156413161 1000000000 9698620928209 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441726811/10000000000 : ℝ)^4999 ≤ (5815269844979/12500000000000 : ℝ)^3975 := by
    have hnat : (5441726811 : ℕ)^4999*12500000000000^3975 ≤ 5815269844979^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441726811 10000000000 5815269844979 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518502707/1000000000 : ℝ)^4999 ≤ (43779220290897/100000000000000 : ℝ)^3975 := by
    have hnat : (518502707 : ℕ)^4999*100000000000000^3975 ≤ 43779220290897^3975*1000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518502707 1000000000 43779220290897 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156413161/1000000000 : ℝ), (5441726811/10000000000 : ℝ), (518502707/1000000000 : ℝ)] ![(9698620928209/100000000000000 : ℝ), (5815269844979/12500000000000 : ℝ), (43779220290897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156413161/1000000000 : ℝ)|^4999 ≤ (9698620928209/100000000000000 : ℝ)^3975
        have hw : |(-156413161/1000000000 : ℝ)|=(156413161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441726811/10000000000 : ℝ)|^4999 ≤ (5815269844979/12500000000000 : ℝ)^3975
        have hw : |(5441726811/10000000000 : ℝ)|=(5441726811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518502707/1000000000 : ℝ)|^4999 ≤ (43779220290897/100000000000000 : ℝ)^3975
        have hw : |(518502707/1000000000 : ℝ)|=(518502707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s3_1 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336177767/2500000000 : ℝ)*x 0 + (-1696177259/10000000000 : ℝ)*x 1 + (5185026817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336177767/2500000000 : ℝ)^4999 ≤ (45481499728633/100000000000000 : ℝ)^3975 := by
    have hnat : (1336177767 : ℕ)^4999*100000000000000^3975 ≤ 45481499728633^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336177767 2500000000 45481499728633 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1696177259/10000000000 : ℝ)^4999 ≤ (10739282652541/100000000000000 : ℝ)^3975 := by
    have hnat : (1696177259 : ℕ)^4999*100000000000000^3975 ≤ 10739282652541^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696177259 10000000000 10739282652541 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185026817/10000000000 : ℝ)^4999 ≤ (43779217604417/100000000000000 : ℝ)^3975 := by
    have hnat : (5185026817 : ℕ)^4999*100000000000000^3975 ≤ 43779217604417^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185026817 10000000000 43779217604417 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336177767/2500000000 : ℝ), (-1696177259/10000000000 : ℝ), (5185026817/10000000000 : ℝ)] ![(45481499728633/100000000000000 : ℝ), (10739282652541/100000000000000 : ℝ), (43779217604417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336177767/2500000000 : ℝ)|^4999 ≤ (45481499728633/100000000000000 : ℝ)^3975
        have hw : |(1336177767/2500000000 : ℝ)|=(1336177767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1696177259/10000000000 : ℝ)|^4999 ≤ (10739282652541/100000000000000 : ℝ)^3975
        have hw : |(-1696177259/10000000000 : ℝ)|=(1696177259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185026817/10000000000 : ℝ)|^4999 ≤ (43779217604417/100000000000000 : ℝ)^3975
        have hw : |(5185026817/10000000000 : ℝ)|=(5185026817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s3_2 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668088907/1250000000 : ℝ)*x 0 + (518502667/1000000000 : ℝ)*x 1 + (-848088601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668088907/1250000000 : ℝ)^4999 ≤ (4548150174057/10000000000000 : ℝ)^3975 := by
    have hnat : (668088907 : ℕ)^4999*10000000000000^3975 ≤ 4548150174057^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668088907 1250000000 4548150174057 10000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518502667/1000000000 : ℝ)^4999 ≤ (21889608021749/50000000000000 : ℝ)^3975 := by
    have hnat : (518502667 : ℕ)^4999*50000000000000^3975 ≤ 21889608021749^3975*1000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518502667 1000000000 21889608021749 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848088601/5000000000 : ℝ)^4999 ≤ (5369641099339/50000000000000 : ℝ)^3975 := by
    have hnat : (848088601 : ℕ)^4999*50000000000000^3975 ≤ 5369641099339^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848088601 5000000000 5369641099339 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668088907/1250000000 : ℝ), (518502667/1000000000 : ℝ), (-848088601/5000000000 : ℝ)] ![(4548150174057/10000000000000 : ℝ), (21889608021749/50000000000000 : ℝ), (5369641099339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668088907/1250000000 : ℝ)|^4999 ≤ (4548150174057/10000000000000 : ℝ)^3975
        have hw : |(668088907/1250000000 : ℝ)|=(668088907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518502667/1000000000 : ℝ)|^4999 ≤ (21889608021749/50000000000000 : ℝ)^3975
        have hw : |(518502667/1000000000 : ℝ)|=(518502667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-848088601/5000000000 : ℝ)|^4999 ≤ (5369641099339/50000000000000 : ℝ)^3975
        have hw : |(-848088601/5000000000 : ℝ)|=(848088601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s3_3 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041414593/2500000000 : ℝ)*x 0 + (3835005149/10000000000 : ℝ)*x 1 + (4515915439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041414593/2500000000 : ℝ)^4999 ≤ (16621887397297/50000000000000 : ℝ)^3975 := by
    have hnat : (1041414593 : ℕ)^4999*50000000000000^3975 ≤ 16621887397297^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041414593 2500000000 16621887397297 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3835005149/10000000000 : ℝ)^4999 ≤ (29959866369487/100000000000000 : ℝ)^3975 := by
    have hnat : (3835005149 : ℕ)^4999*100000000000000^3975 ≤ 29959866369487^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3835005149 10000000000 29959866369487 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515915439/10000000000 : ℝ)^4999 ≤ (18398179409901/50000000000000 : ℝ)^3975 := by
    have hnat : (4515915439 : ℕ)^4999*50000000000000^3975 ≤ 18398179409901^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515915439 10000000000 18398179409901 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041414593/2500000000 : ℝ), (3835005149/10000000000 : ℝ), (4515915439/10000000000 : ℝ)] ![(16621887397297/50000000000000 : ℝ), (29959866369487/100000000000000 : ℝ), (18398179409901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041414593/2500000000 : ℝ)|^4999 ≤ (16621887397297/50000000000000 : ℝ)^3975
        have hw : |(1041414593/2500000000 : ℝ)|=(1041414593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3835005149/10000000000 : ℝ)|^4999 ≤ (29959866369487/100000000000000 : ℝ)^3975
        have hw : |(3835005149/10000000000 : ℝ)|=(3835005149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515915439/10000000000 : ℝ)|^4999 ≤ (18398179409901/50000000000000 : ℝ)^3975
        have hw : |(4515915439/10000000000 : ℝ)|=(4515915439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s3_4 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-391048323/2500000000 : ℝ)*x 0 + (2593493259/5000000000 : ℝ)*x 1 + (5439746679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391048323/2500000000 : ℝ)^4999 ≤ (1212387740787/12500000000000 : ℝ)^3975 := by
    have hnat : (391048323 : ℕ)^4999*12500000000000^3975 ≤ 1212387740787^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391048323 2500000000 1212387740787 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593493259/5000000000 : ℝ)^4999 ≤ (8760005538773/20000000000000 : ℝ)^3975 := by
    have hnat : (2593493259 : ℕ)^4999*20000000000000^3975 ≤ 8760005538773^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593493259 5000000000 8760005538773 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439746679/10000000000 : ℝ)^4999 ≤ (46500870365201/100000000000000 : ℝ)^3975 := by
    have hnat : (5439746679 : ℕ)^4999*100000000000000^3975 ≤ 46500870365201^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439746679 10000000000 46500870365201 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391048323/2500000000 : ℝ), (2593493259/5000000000 : ℝ), (5439746679/10000000000 : ℝ)] ![(1212387740787/12500000000000 : ℝ), (8760005538773/20000000000000 : ℝ), (46500870365201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391048323/2500000000 : ℝ)|^4999 ≤ (1212387740787/12500000000000 : ℝ)^3975
        have hw : |(-391048323/2500000000 : ℝ)|=(391048323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593493259/5000000000 : ℝ)|^4999 ≤ (8760005538773/20000000000000 : ℝ)^3975
        have hw : |(2593493259/5000000000 : ℝ)|=(2593493259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439746679/10000000000 : ℝ)|^4999 ≤ (46500870365201/100000000000000 : ℝ)^3975
        have hw : |(5439746679/10000000000 : ℝ)|=(5439746679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s3_5 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637994077/5000000000 : ℝ)*x 0 + (-720728671/5000000000 : ℝ)*x 1 + (5439746687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637994077/5000000000 : ℝ)^4999 ≤ (349587994391/781250000000 : ℝ)^3975 := by
    have hnat : (2637994077 : ℕ)^4999*781250000000^3975 ≤ 349587994391^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637994077 5000000000 349587994391 781250000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720728671/5000000000 : ℝ)^4999 ≤ (8751866249699/100000000000000 : ℝ)^3975 := by
    have hnat : (720728671 : ℕ)^4999*100000000000000^3975 ≤ 8751866249699^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720728671 5000000000 8751866249699 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439746687/10000000000 : ℝ)^4999 ≤ (11625217612801/25000000000000 : ℝ)^3975 := by
    have hnat : (5439746687 : ℕ)^4999*25000000000000^3975 ≤ 11625217612801^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439746687 10000000000 11625217612801 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637994077/5000000000 : ℝ), (-720728671/5000000000 : ℝ), (5439746687/10000000000 : ℝ)] ![(349587994391/781250000000 : ℝ), (8751866249699/100000000000000 : ℝ), (11625217612801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637994077/5000000000 : ℝ)|^4999 ≤ (349587994391/781250000000 : ℝ)^3975
        have hw : |(2637994077/5000000000 : ℝ)|=(2637994077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-720728671/5000000000 : ℝ)|^4999 ≤ (8751866249699/100000000000000 : ℝ)^3975
        have hw : |(-720728671/5000000000 : ℝ)|=(720728671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439746687/10000000000 : ℝ)|^4999 ≤ (11625217612801/25000000000000 : ℝ)^3975
        have hw : |(5439746687/10000000000 : ℝ)|=(5439746687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s3_6 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318997043/2500000000 : ℝ)*x 0 + (5439746679/10000000000 : ℝ)*x 1 + (-90091083/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318997043/2500000000 : ℝ)^4999 ≤ (44747263474039/100000000000000 : ℝ)^3975 := by
    have hnat : (1318997043 : ℕ)^4999*100000000000000^3975 ≤ 44747263474039^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318997043 2500000000 44747263474039 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439746679/10000000000 : ℝ)^4999 ≤ (46500870365201/100000000000000 : ℝ)^3975 := by
    have hnat : (5439746679 : ℕ)^4999*100000000000000^3975 ≤ 46500870365201^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439746679 10000000000 46500870365201 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90091083/625000000 : ℝ)^4999 ≤ (8751866142801/100000000000000 : ℝ)^3975 := by
    have hnat : (90091083 : ℕ)^4999*100000000000000^3975 ≤ 8751866142801^3975*625000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90091083 625000000 8751866142801 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318997043/2500000000 : ℝ), (5439746679/10000000000 : ℝ), (-90091083/625000000 : ℝ)] ![(44747263474039/100000000000000 : ℝ), (46500870365201/100000000000000 : ℝ), (8751866142801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318997043/2500000000 : ℝ)|^4999 ≤ (44747263474039/100000000000000 : ℝ)^3975
        have hw : |(1318997043/2500000000 : ℝ)|=(1318997043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439746679/10000000000 : ℝ)|^4999 ≤ (46500870365201/100000000000000 : ℝ)^3975
        have hw : |(5439746679/10000000000 : ℝ)|=(5439746679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90091083/625000000 : ℝ)|^4999 ≤ (8751866142801/100000000000000 : ℝ)^3975
        have hw : |(-90091083/625000000 : ℝ)|=(90091083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s3_7 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5207277/12500000 : ℝ)*x 0 + (4510717153/10000000000 : ℝ)*x 1 + (3840258497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5207277/12500000 : ℝ)^4999 ≤ (33245413004457/100000000000000 : ℝ)^3975 := by
    have hnat : (5207277 : ℕ)^4999*100000000000000^3975 ≤ 33245413004457^3975*12500000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207277 12500000 33245413004457 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510717153/10000000000 : ℝ)^4999 ≤ (18371549431939/50000000000000 : ℝ)^3975 := by
    have hnat : (4510717153 : ℕ)^4999*50000000000000^3975 ≤ 18371549431939^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510717153 10000000000 18371549431939 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3840258497/10000000000 : ℝ)^4999 ≤ (15005744057799/50000000000000 : ℝ)^3975 := by
    have hnat : (3840258497 : ℕ)^4999*50000000000000^3975 ≤ 15005744057799^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3840258497 10000000000 15005744057799 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5207277/12500000 : ℝ), (4510717153/10000000000 : ℝ), (3840258497/10000000000 : ℝ)] ![(33245413004457/100000000000000 : ℝ), (18371549431939/50000000000000 : ℝ), (15005744057799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5207277/12500000 : ℝ)|^4999 ≤ (33245413004457/100000000000000 : ℝ)^3975
        have hw : |(5207277/12500000 : ℝ)|=(5207277/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510717153/10000000000 : ℝ)|^4999 ≤ (18371549431939/50000000000000 : ℝ)^3975
        have hw : |(4510717153/10000000000 : ℝ)|=(4510717153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3840258497/10000000000 : ℝ)|^4999 ≤ (15005744057799/50000000000000 : ℝ)^3975
        have hw : |(3840258497/10000000000 : ℝ)|=(3840258497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1670_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5383/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16231/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10719/100000 : ℝ) ^ (4995/1024 : ℝ) ≤ (929246063866929/50000000000000000000 : ℝ) := by
    have hpowers : (10719/100000 : ℝ)^4995 ≤ (929246063866929/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10719 : ℕ)^4995*50000000000000000000^1024 ≤ 929246063866929^1024*100000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10719 100000 929246063866929 50000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10719/100000 : ℝ)) (X := (929246063866929/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16283/100000 : ℝ) ^ (4995/1024 : ℝ) ≤ (1428551625578577/10000000000000000000 : ℝ) := by
    have hpowers : (16283/100000 : ℝ)^4995 ≤ (1428551625578577/10000000000000000000 : ℝ)^1024 := by
      have hnat : (16283 : ℕ)^4995*10000000000000000000^1024 ≤ 1428551625578577^1024*100000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16283 100000 1428551625578577 10000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16283/100000 : ℝ)) (X := (1428551625578577/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000929246063866929/25000000000000000000 : ℝ) ≤ (5000038099455883/5000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (25000929246063866929/25000000000000000000 : ℝ)^1024 ≤ (5000038099455883/5000000000000000 : ℝ)^4995 := by
      have hnat : (25000929246063866929 : ℕ)^1024*5000000000000000^4995 ≤ 5000038099455883^4995*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000929246063866929 25000000000000000000 5000038099455883 5000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038099455883/5000000000000000 : ℝ)) (X := (25000929246063866929/25000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004036002095879907/25000000000000000000 : ℝ) ≤ (10000330939015607/10000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (25004036002095879907/25000000000000000000 : ℝ)^1024 ≤ (10000330939015607/10000000000000000 : ℝ)^4995 := by
      have hnat : (25004036002095879907 : ℕ)^1024*10000000000000000^4995 ≤ 10000330939015607^4995*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004036002095879907 25000000000000000000 10000330939015607 10000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000330939015607/10000000000000000 : ℝ)) (X := (25004036002095879907/25000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001428551625578577/5000000000000000000 : ℝ) ≤ (1250073209889931/1250000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (5001428551625578577/5000000000000000000 : ℝ)^1024 ≤ (1250073209889931/1250000000000000 : ℝ)^4995 := by
      have hnat : (5001428551625578577 : ℕ)^1024*1250000000000000^4995 ≤ 1250073209889931^4995*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001428551625578577 5000000000000000000 1250073209889931 1250000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250073209889931/1250000000000000 : ℝ)) (X := (5001428551625578577/5000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(929246063866929/50000000000000000000 : ℝ) ≤ ((27817481426199461333/27820000000000000000 : ℝ)+2*(254740103841/556400000000000 : ℝ)*(10719/100000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (27817481426199461333/27820000000000000000 : ℝ)+2*(254740103841/556400000000000 : ℝ)*(10719/100000 : ℝ)=(5000038099455883/5000000000000000 : ℝ) by norm_num, show 1+2*(929246063866929/50000000000000000000 : ℝ)=(25000929246063866929/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1428551625578577/10000000000000000000 : ℝ)+(929246063866929/50000000000000000000 : ℝ) ≤ ((27817481426199461333/27820000000000000000 : ℝ)+(254740103841/556400000000000 : ℝ)*((16283/100000 : ℝ)+(10719/100000 : ℝ)))^(4995/1024 : ℝ) := by
    rw [show (27817481426199461333/27820000000000000000 : ℝ)+(254740103841/556400000000000 : ℝ)*((16283/100000 : ℝ)+(10719/100000 : ℝ))=(10000330939015607/10000000000000000 : ℝ) by norm_num, show 1+(1428551625578577/10000000000000000000 : ℝ)+(929246063866929/50000000000000000000 : ℝ)=(25004036002095879907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1428551625578577/10000000000000000000 : ℝ) ≤ ((27817481426199461333/27820000000000000000 : ℝ)+2*(254740103841/556400000000000 : ℝ)*(16283/100000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (27817481426199461333/27820000000000000000 : ℝ)+2*(254740103841/556400000000000 : ℝ)*(16283/100000 : ℝ)=(1250073209889931/1250000000000000 : ℝ) by norm_num, show 1+2*(1428551625578577/10000000000000000000 : ℝ)=(5001428551625578577/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27817481426199461333/27820000000000000000 : ℝ)*(X 1 0+X 2 0)+(254740103841/556400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (27817481426199461333/27820000000000000000 : ℝ)) (alpha := (254740103841/556400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27817481426199461333/27820000000000000000 : ℝ)*(X 0 1+X 2 1)+(254740103841/556400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (27817481426199461333/27820000000000000000 : ℝ)) (alpha := (254740103841/556400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27817481426199461333/27820000000000000000 : ℝ)*(X 0 2+X 1 2)+(254740103841/556400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (27817481426199461333/27820000000000000000 : ℝ)) (alpha := (254740103841/556400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-156413161/1000000000 : ℝ)*X 0 0+(5441726811/10000000000 : ℝ)*X 0 1+(518502707/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336177767/2500000000 : ℝ)*X 1 0+(-1696177259/10000000000 : ℝ)*X 1 1+(5185026817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668088907/1250000000 : ℝ)*X 2 0+(518502667/1000000000 : ℝ)*X 2 1+(-848088601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1041414593/2500000000 : ℝ)*X 0 0+(3835005149/10000000000 : ℝ)*X 0 1+(4515915439/10000000000 : ℝ)*X 0 2+(1041414593/2500000000 : ℝ)*X 1 0+(3835005149/10000000000 : ℝ)*X 1 1+(4515915439/10000000000 : ℝ)*X 1 2+(1041414593/2500000000 : ℝ)*X 2 0+(3835005149/10000000000 : ℝ)*X 2 1+(4515915439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-391048323/2500000000 : ℝ)*X 0 0+(2593493259/5000000000 : ℝ)*X 0 1+(5439746679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2637994077/5000000000 : ℝ)*X 1 0+(-720728671/5000000000 : ℝ)*X 1 1+(5439746687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1318997043/2500000000 : ℝ)*X 2 0+(5439746679/10000000000 : ℝ)*X 2 1+(-90091083/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((5207277/12500000 : ℝ)*X 0 0+(4510717153/10000000000 : ℝ)*X 0 1+(3840258497/10000000000 : ℝ)*X 0 2+(5207277/12500000 : ℝ)*X 1 0+(4510717153/10000000000 : ℝ)*X 1 1+(3840258497/10000000000 : ℝ)*X 1 2+(5207277/12500000 : ℝ)*X 2 0+(4510717153/10000000000 : ℝ)*X 2 1+(3840258497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (545409292373238147146593197/53500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66604427/4000000000000 : ℝ)*(base19) + (319696897/20000000000000 : ℝ)*(base23) + (27211923/25000000000000 : ℝ)*(lower2) + (133480477/50000000000000 : ℝ)*(upper3) + (187198617/100000000000000 : ℝ)*(upper5) + (2682137309360561/100000000000000 : ℝ)*(major0) + (2682137309360561/100000000000000 : ℝ)*(major1) + (2682137309360561/100000000000000 : ℝ)*(major2) + (779123678868709/20000000000000 : ℝ)*(sp0) + (155825354198307/4000000000000 : ℝ)*(sp1) + (1947816960791933/50000000000000 : ℝ)*(sp2) + (734314884031901/50000000000000 : ℝ)*(sp3) + (3425144961/20000000000000 : ℝ)*(sp4) + (899077009/10000000000000 : ℝ)*(sp7) + (367159689708473/25000000000000 : ℝ)*(f.failure) + (77912710401367/2000000000000 : ℝ)*(f.sum) + (8742510757917/2140000000000000000000000000 : ℝ)*base65 + (897662421982210601/214000000000000000000000000000000 : ℝ)*base67 + (345286627782210601/214000000000000000000000000000000 : ℝ)*base69 + (176084074091789399/214000000000000000000000000000000 : ℝ)*base72 + (2590776465343/2140000000000000000000000000 : ℝ)*base74 + (1607130195562210601/214000000000000000000000000000000 : ℝ)*base75 + (313088083564210601/214000000000000000000000000000000 : ℝ)*base77 + (947472583692210601/214000000000000000000000000000000 : ℝ)*base79 + (160806788037/2140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3383693/625000000000000000000 : ℝ)*base90 + (3383693/625000000000000000000 : ℝ)*base92 + (3383693/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3725586333094973304599682873/278200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1931627067/100000000000000 : ℝ)*(base19) + (1050598401/50000000000000 : ℝ)*(base23) + (70669309/25000000000000 : ℝ)*(upper3) + (68697073/100000000000000 : ℝ)*(lower4) + (277450369/100000000000000 : ℝ)*(upper5) + (544783503938291/20000000000000 : ℝ)*(major0) + (544783503938291/20000000000000 : ℝ)*(major1) + (544783503938291/20000000000000 : ℝ)*(major2) + (23608629019/100000000000000 : ℝ)*(sp1) + (1023770861/4000000000000 : ℝ)*(sp2) + (989079635741197/25000000000000 : ℝ)*(sp4) + (1978146501354351/50000000000000 : ℝ)*(sp5) + (3956290847496461/100000000000000 : ℝ)*(sp6) + (149151605002627/10000000000000 : ℝ)*(sp7) + (149151605002627/10000000000000 : ℝ)*(f.failure) + (989079635741197/25000000000000 : ℝ)*(f.sum) + (209495418319/44512000000000000000000000 : ℝ)*base65 + (1226459650397551903/556400000000000000000000000000000 : ℝ)*base67 + (4805158935410351903/556400000000000000000000000000000 : ℝ)*base69 + (2318176037499151903/556400000000000000000000000000000 : ℝ)*base71 + (33656539418711/5564000000000000000000000000 : ℝ)*base73 + (1737706959692351903/556400000000000000000000000000000 : ℝ)*base75 + (640270440630351903/556400000000000000000000000000000 : ℝ)*base77 + (3212336610503551903/556400000000000000000000000000000 : ℝ)*base79 + (10475320626083/5564000000000000000000000000 : ℝ)*base81 + (1931407/250000000000000000000 : ℝ)*base90 + (1931407/250000000000000000000 : ℝ)*base92 + (1931407/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1670_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5383/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1670_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1670_s4_0 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156415927/1000000000 : ℝ)*x 0 + (2720792341/5000000000 : ℝ)*x 1 + (2592575333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156415927/1000000000 : ℝ)^4999 ≤ (1939767324223/20000000000000 : ℝ)^3975 := by
    have hnat : (156415927 : ℕ)^4999*20000000000000^3975 ≤ 1939767324223^3975*1000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156415927 1000000000 1939767324223 20000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720792341/5000000000 : ℝ)^4999 ≤ (46520630664789/100000000000000 : ℝ)^3975 := by
    have hnat : (2720792341 : ℕ)^4999*100000000000000^3975 ≤ 46520630664789^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720792341 5000000000 46520630664789 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592575333/5000000000 : ℝ)^4999 ≤ (43780532698529/100000000000000 : ℝ)^3975 := by
    have hnat : (2592575333 : ℕ)^4999*100000000000000^3975 ≤ 43780532698529^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592575333 5000000000 43780532698529 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156415927/1000000000 : ℝ), (2720792341/5000000000 : ℝ), (2592575333/5000000000 : ℝ)] ![(1939767324223/20000000000000 : ℝ), (46520630664789/100000000000000 : ℝ), (43780532698529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156415927/1000000000 : ℝ)|^4999 ≤ (1939767324223/20000000000000 : ℝ)^3975
        have hw : |(-156415927/1000000000 : ℝ)|=(156415927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720792341/5000000000 : ℝ)|^4999 ≤ (46520630664789/100000000000000 : ℝ)^3975
        have hw : |(2720792341/5000000000 : ℝ)|=(2720792341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592575333/5000000000 : ℝ)|^4999 ≤ (43780532698529/100000000000000 : ℝ)^3975
        have hw : |(2592575333/5000000000 : ℝ)|=(2592575333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s4_1 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336168089/2500000000 : ℝ)*x 0 + (-1696064151/10000000000 : ℝ)*x 1 + (648143831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336168089/2500000000 : ℝ)^4999 ≤ (45481085441207/100000000000000 : ℝ)^3975 := by
    have hnat : (1336168089 : ℕ)^4999*100000000000000^3975 ≤ 45481085441207^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336168089 2500000000 45481085441207 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1696064151/10000000000 : ℝ)^4999 ≤ (671148877287/6250000000000 : ℝ)^3975 := by
    have hnat : (1696064151 : ℕ)^4999*6250000000000^3975 ≤ 671148877287^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696064151 10000000000 671148877287 6250000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648143831/1250000000 : ℝ)^4999 ≤ (21890266253697/50000000000000 : ℝ)^3975 := by
    have hnat : (648143831 : ℕ)^4999*50000000000000^3975 ≤ 21890266253697^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648143831 1250000000 21890266253697 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336168089/2500000000 : ℝ), (-1696064151/10000000000 : ℝ), (648143831/1250000000 : ℝ)] ![(45481085441207/100000000000000 : ℝ), (671148877287/6250000000000 : ℝ), (21890266253697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336168089/2500000000 : ℝ)|^4999 ≤ (45481085441207/100000000000000 : ℝ)^3975
        have hw : |(1336168089/2500000000 : ℝ)|=(1336168089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1696064151/10000000000 : ℝ)|^4999 ≤ (671148877287/6250000000000 : ℝ)^3975
        have hw : |(-1696064151/10000000000 : ℝ)|=(1696064151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648143831/1250000000 : ℝ)|^4999 ≤ (21890266253697/50000000000000 : ℝ)^3975
        have hw : |(648143831/1250000000 : ℝ)|=(648143831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s4_2 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344672473/10000000000 : ℝ)*x 0 + (648143821/1250000000 : ℝ)*x 1 + (-1696064101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344672473/10000000000 : ℝ)^4999 ≤ (22740543346657/50000000000000 : ℝ)^3975 := by
    have hnat : (5344672473 : ℕ)^4999*50000000000000^3975 ≤ 22740543346657^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344672473 10000000000 22740543346657 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648143821/1250000000 : ℝ)^4999 ≤ (4378053165791/10000000000000 : ℝ)^3975 := by
    have hnat : (648143821 : ℕ)^4999*10000000000000^3975 ≤ 4378053165791^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648143821 1250000000 4378053165791 10000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1696064101/10000000000 : ℝ)^4999 ≤ (5369190819237/50000000000000 : ℝ)^3975 := by
    have hnat : (1696064101 : ℕ)^4999*50000000000000^3975 ≤ 5369190819237^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696064101 10000000000 5369190819237 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344672473/10000000000 : ℝ), (648143821/1250000000 : ℝ), (-1696064101/10000000000 : ℝ)] ![(22740543346657/50000000000000 : ℝ), (4378053165791/10000000000000 : ℝ), (5369190819237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344672473/10000000000 : ℝ)|^4999 ≤ (22740543346657/50000000000000 : ℝ)^3975
        have hw : |(5344672473/10000000000 : ℝ)|=(5344672473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648143821/1250000000 : ℝ)|^4999 ≤ (4378053165791/10000000000000 : ℝ)^3975
        have hw : |(648143821/1250000000 : ℝ)|=(648143821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1696064101/10000000000 : ℝ)|^4999 ≤ (5369190819237/50000000000000 : ℝ)^3975
        have hw : |(-1696064101/10000000000 : ℝ)|=(1696064101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s4_3 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416567669/1000000000 : ℝ)*x 0 + (3835356713/10000000000 : ℝ)*x 1 + (4515560421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416567669/1000000000 : ℝ)^4999 ≤ (831098965981/2500000000000 : ℝ)^3975 := by
    have hnat : (416567669 : ℕ)^4999*2500000000000^3975 ≤ 831098965981^3975*1000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416567669 1000000000 831098965981 2500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3835356713/10000000000 : ℝ)^4999 ≤ (7490830106521/25000000000000 : ℝ)^3975 := by
    have hnat : (3835356713 : ℕ)^4999*25000000000000^3975 ≤ 7490830106521^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3835356713 10000000000 7490830106521 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515560421/10000000000 : ℝ)^4999 ≤ (36792720917571/100000000000000 : ℝ)^3975 := by
    have hnat : (4515560421 : ℕ)^4999*100000000000000^3975 ≤ 36792720917571^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515560421 10000000000 36792720917571 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416567669/1000000000 : ℝ), (3835356713/10000000000 : ℝ), (4515560421/10000000000 : ℝ)] ![(831098965981/2500000000000 : ℝ), (7490830106521/25000000000000 : ℝ), (36792720917571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416567669/1000000000 : ℝ)|^4999 ≤ (831098965981/2500000000000 : ℝ)^3975
        have hw : |(416567669/1000000000 : ℝ)|=(416567669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3835356713/10000000000 : ℝ)|^4999 ≤ (7490830106521/25000000000000 : ℝ)^3975
        have hw : |(3835356713/10000000000 : ℝ)|=(3835356713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515560421/10000000000 : ℝ)|^4999 ≤ (36792720917571/100000000000000 : ℝ)^3975
        have hw : |(4515560421/10000000000 : ℝ)|=(4515560421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s4_4 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-78211039/500000000 : ℝ)*x 0 + (5187106337/10000000000 : ℝ)*x 1 + (271980419/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78211039/500000000 : ℝ)^4999 ≤ (9699316280119/100000000000000 : ℝ)^3975 := by
    have hnat : (78211039 : ℕ)^4999*100000000000000^3975 ≤ 9699316280119^3975*500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78211039 500000000 9699316280119 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187106337/10000000000 : ℝ)^4999 ≤ (21900650059519/50000000000000 : ℝ)^3975 := by
    have hnat : (5187106337 : ℕ)^4999*50000000000000^3975 ≤ 21900650059519^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187106337 10000000000 21900650059519 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271980419/500000000 : ℝ)^4999 ≤ (46499383587539/100000000000000 : ℝ)^3975 := by
    have hnat : (271980419 : ℕ)^4999*100000000000000^3975 ≤ 46499383587539^3975*500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271980419 500000000 46499383587539 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78211039/500000000 : ℝ), (5187106337/10000000000 : ℝ), (271980419/500000000 : ℝ)] ![(9699316280119/100000000000000 : ℝ), (21900650059519/50000000000000 : ℝ), (46499383587539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78211039/500000000 : ℝ)|^4999 ≤ (9699316280119/100000000000000 : ℝ)^3975
        have hw : |(-78211039/500000000 : ℝ)|=(78211039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187106337/10000000000 : ℝ)|^4999 ≤ (21900650059519/50000000000000 : ℝ)^3975
        have hw : |(5187106337/10000000000 : ℝ)|=(5187106337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271980419/500000000 : ℝ)|^4999 ≤ (46499383587539/100000000000000 : ℝ)^3975
        have hw : |(271980419/500000000 : ℝ)|=(271980419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s4_5 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276020817/10000000000 : ℝ)*x 0 + (-360401597/2500000000 : ℝ)*x 1 + (5439608417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276020817/10000000000 : ℝ)^4999 ≤ (11186902917893/25000000000000 : ℝ)^3975 := by
    have hnat : (5276020817 : ℕ)^4999*25000000000000^3975 ≤ 11186902917893^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276020817 10000000000 11186902917893 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360401597/2500000000 : ℝ)^4999 ≤ (437650216249/5000000000000 : ℝ)^3975 := by
    have hnat : (360401597 : ℕ)^4999*5000000000000^3975 ≤ 437650216249^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360401597 2500000000 437650216249 5000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439608417/10000000000 : ℝ)^4999 ≤ (5812422998163/12500000000000 : ℝ)^3975 := by
    have hnat : (5439608417 : ℕ)^4999*12500000000000^3975 ≤ 5812422998163^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439608417 10000000000 5812422998163 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276020817/10000000000 : ℝ), (-360401597/2500000000 : ℝ), (5439608417/10000000000 : ℝ)] ![(11186902917893/25000000000000 : ℝ), (437650216249/5000000000000 : ℝ), (5812422998163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276020817/10000000000 : ℝ)|^4999 ≤ (11186902917893/25000000000000 : ℝ)^3975
        have hw : |(5276020817/10000000000 : ℝ)|=(5276020817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360401597/2500000000 : ℝ)|^4999 ≤ (437650216249/5000000000000 : ℝ)^3975
        have hw : |(-360401597/2500000000 : ℝ)|=(360401597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439608417/10000000000 : ℝ)|^4999 ≤ (5812422998163/12500000000000 : ℝ)^3975
        have hw : |(5439608417/10000000000 : ℝ)|=(5439608417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s4_6 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276020833/10000000000 : ℝ)*x 0 + (2719804193/5000000000 : ℝ)*x 1 + (-144160641/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276020833/10000000000 : ℝ)^4999 ≤ (44747611842231/100000000000000 : ℝ)^3975 := by
    have hnat : (5276020833 : ℕ)^4999*100000000000000^3975 ≤ 44747611842231^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276020833 10000000000 44747611842231 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719804193/5000000000 : ℝ)^4999 ≤ (46499383652041/100000000000000 : ℝ)^3975 := by
    have hnat : (2719804193 : ℕ)^4999*100000000000000^3975 ≤ 46499383652041^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719804193 5000000000 46499383652041 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144160641/1000000000 : ℝ)^4999 ≤ (1094125561621/12500000000000 : ℝ)^3975 := by
    have hnat : (144160641 : ℕ)^4999*12500000000000^3975 ≤ 1094125561621^3975*1000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144160641 1000000000 1094125561621 12500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276020833/10000000000 : ℝ), (2719804193/5000000000 : ℝ), (-144160641/1000000000 : ℝ)] ![(44747611842231/100000000000000 : ℝ), (46499383652041/100000000000000 : ℝ), (1094125561621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276020833/10000000000 : ℝ)|^4999 ≤ (44747611842231/100000000000000 : ℝ)^3975
        have hw : |(5276020833/10000000000 : ℝ)|=(5276020833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719804193/5000000000 : ℝ)|^4999 ≤ (46499383652041/100000000000000 : ℝ)^3975
        have hw : |(2719804193/5000000000 : ℝ)|=(2719804193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-144160641/1000000000 : ℝ)|^4999 ≤ (1094125561621/12500000000000 : ℝ)^3975
        have hw : |(-144160641/1000000000 : ℝ)|=(144160641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s4_7 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165839599/10000000000 : ℝ)*x 0 + (2255186443/5000000000 : ℝ)*x 1 + (960149737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165839599/10000000000 : ℝ)^4999 ≤ (664911872987/2000000000000 : ℝ)^3975 := by
    have hnat : (4165839599 : ℕ)^4999*2000000000000^3975 ≤ 664911872987^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165839599 10000000000 664911872987 2000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255186443/5000000000 : ℝ)^4999 ≤ (36739572173643/100000000000000 : ℝ)^3975 := by
    have hnat : (2255186443 : ℕ)^4999*100000000000000^3975 ≤ 36739572173643^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255186443 5000000000 36739572173643 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960149737/2500000000 : ℝ)^4999 ≤ (30014834167311/100000000000000 : ℝ)^3975 := by
    have hnat : (960149737 : ℕ)^4999*100000000000000^3975 ≤ 30014834167311^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960149737 2500000000 30014834167311 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165839599/10000000000 : ℝ), (2255186443/5000000000 : ℝ), (960149737/2500000000 : ℝ)] ![(664911872987/2000000000000 : ℝ), (36739572173643/100000000000000 : ℝ), (30014834167311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165839599/10000000000 : ℝ)|^4999 ≤ (664911872987/2000000000000 : ℝ)^3975
        have hw : |(4165839599/10000000000 : ℝ)|=(4165839599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255186443/5000000000 : ℝ)|^4999 ≤ (36739572173643/100000000000000 : ℝ)^3975
        have hw : |(2255186443/5000000000 : ℝ)|=(2255186443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(960149737/2500000000 : ℝ)|^4999 ≤ (30014834167311/100000000000000 : ℝ)^3975
        have hw : |(960149737/2500000000 : ℝ)|=(960149737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1670_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10769/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4057/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16231/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16231/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16231/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16231/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16231/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16231/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5383/50000 : ℝ) ^ (4995/1024 : ℝ) ≤ (379716350295521/20000000000000000000 : ℝ) := by
    have hpowers : (5383/50000 : ℝ)^4995 ≤ (379716350295521/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5383 : ℕ)^4995*20000000000000000000^1024 ≤ 379716350295521^1024*50000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5383 50000 379716350295521 20000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5383/50000 : ℝ)) (X := (379716350295521/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16231/100000 : ℝ) ^ (4995/1024 : ℝ) ≤ (2812870789613673/20000000000000000000 : ℝ) := by
    have hpowers : (16231/100000 : ℝ)^4995 ≤ (2812870789613673/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16231 : ℕ)^4995*20000000000000000000^1024 ≤ 2812870789613673^1024*100000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16231 100000 2812870789613673 20000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16231/100000 : ℝ)) (X := (2812870789613673/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000379716350295521/10000000000000000000 : ℝ) ≤ (80000622740619/80000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (10000379716350295521/10000000000000000000 : ℝ)^1024 ≤ (80000622740619/80000000000000 : ℝ)^4995 := by
      have hnat : (10000379716350295521 : ℕ)^1024*80000000000000^4995 ≤ 80000622740619^4995*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000379716350295521 10000000000000000000 80000622740619 80000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80000622740619/80000000000000 : ℝ)) (X := (10000379716350295521/10000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001596293569954597/10000000000000000000 : ℝ) ≤ (5000163613704321/5000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (10001596293569954597/10000000000000000000 : ℝ)^1024 ≤ (5000163613704321/5000000000000000 : ℝ)^4995 := by
      have hnat : (10001596293569954597 : ℕ)^1024*5000000000000000^4995 ≤ 5000163613704321^4995*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001596293569954597 10000000000000000000 5000163613704321 5000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000163613704321/5000000000000000 : ℝ)) (X := (10001596293569954597/10000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002812870789613673/10000000000000000000 : ℝ) ≤ (10000576612239909/10000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (10002812870789613673/10000000000000000000 : ℝ)^1024 ≤ (10000576612239909/10000000000000000 : ℝ)^4995 := by
      have hnat : (10002812870789613673 : ℕ)^1024*10000000000000000^4995 ≤ 10000576612239909^4995*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002812870789613673 10000000000000000000 10000576612239909 10000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000576612239909/10000000000000000 : ℝ)) (X := (10002812870789613673/10000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(379716350295521/20000000000000000000 : ℝ) ≤ ((54645055655498513331/54650000000000000000 : ℝ)+2*(249384831267/546500000000000 : ℝ)*(5383/50000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (54645055655498513331/54650000000000000000 : ℝ)+2*(249384831267/546500000000000 : ℝ)*(5383/50000 : ℝ)=(80000622740619/80000000000000 : ℝ) by norm_num, show 1+2*(379716350295521/20000000000000000000 : ℝ)=(10000379716350295521/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2812870789613673/20000000000000000000 : ℝ)+(379716350295521/20000000000000000000 : ℝ) ≤ ((54645055655498513331/54650000000000000000 : ℝ)+(249384831267/546500000000000 : ℝ)*((16231/100000 : ℝ)+(5383/50000 : ℝ)))^(4995/1024 : ℝ) := by
    rw [show (54645055655498513331/54650000000000000000 : ℝ)+(249384831267/546500000000000 : ℝ)*((16231/100000 : ℝ)+(5383/50000 : ℝ))=(5000163613704321/5000000000000000 : ℝ) by norm_num, show 1+(2812870789613673/20000000000000000000 : ℝ)+(379716350295521/20000000000000000000 : ℝ)=(10001596293569954597/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2812870789613673/20000000000000000000 : ℝ) ≤ ((54645055655498513331/54650000000000000000 : ℝ)+2*(249384831267/546500000000000 : ℝ)*(16231/100000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (54645055655498513331/54650000000000000000 : ℝ)+2*(249384831267/546500000000000 : ℝ)*(16231/100000 : ℝ)=(10000576612239909/10000000000000000 : ℝ) by norm_num, show 1+2*(2812870789613673/20000000000000000000 : ℝ)=(10002812870789613673/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54645055655498513331/54650000000000000000 : ℝ)*(X 1 0+X 2 0)+(249384831267/546500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (5383/50000 : ℝ)) (hi := (16231/100000 : ℝ)) (c := (54645055655498513331/54650000000000000000 : ℝ)) (alpha := (249384831267/546500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54645055655498513331/54650000000000000000 : ℝ)*(X 0 1+X 2 1)+(249384831267/546500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (5383/50000 : ℝ)) (hi := (16231/100000 : ℝ)) (c := (54645055655498513331/54650000000000000000 : ℝ)) (alpha := (249384831267/546500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54645055655498513331/54650000000000000000 : ℝ)*(X 0 2+X 1 2)+(249384831267/546500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (5383/50000 : ℝ)) (hi := (16231/100000 : ℝ)) (c := (54645055655498513331/54650000000000000000 : ℝ)) (alpha := (249384831267/546500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-156415927/1000000000 : ℝ)*X 0 0+(2720792341/5000000000 : ℝ)*X 0 1+(2592575333/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336168089/2500000000 : ℝ)*X 1 0+(-1696064151/10000000000 : ℝ)*X 1 1+(648143831/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344672473/10000000000 : ℝ)*X 2 0+(648143821/1250000000 : ℝ)*X 2 1+(-1696064101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((416567669/1000000000 : ℝ)*X 0 0+(3835356713/10000000000 : ℝ)*X 0 1+(4515560421/10000000000 : ℝ)*X 0 2+(416567669/1000000000 : ℝ)*X 1 0+(3835356713/10000000000 : ℝ)*X 1 1+(4515560421/10000000000 : ℝ)*X 1 2+(416567669/1000000000 : ℝ)*X 2 0+(3835356713/10000000000 : ℝ)*X 2 1+(4515560421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-78211039/500000000 : ℝ)*X 0 0+(5187106337/10000000000 : ℝ)*X 0 1+(271980419/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276020817/10000000000 : ℝ)*X 1 0+(-360401597/2500000000 : ℝ)*X 1 1+(5439608417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276020833/10000000000 : ℝ)*X 2 0+(2719804193/5000000000 : ℝ)*X 2 1+(-144160641/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4165839599/10000000000 : ℝ)*X 0 0+(2255186443/5000000000 : ℝ)*X 0 1+(960149737/2500000000 : ℝ)*X 0 2+(4165839599/10000000000 : ℝ)*X 1 0+(2255186443/5000000000 : ℝ)*X 1 1+(960149737/2500000000 : ℝ)*X 1 2+(4165839599/10000000000 : ℝ)*X 2 0+(2255186443/5000000000 : ℝ)*X 2 1+(960149737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4587704497060752326375048253/683125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (535247551/50000000000000 : ℝ)*(base19) + (1004400453/100000000000000 : ℝ)*(base23) + (80951497/100000000000000 : ℝ)*(lower2) + (160907717/100000000000000 : ℝ)*(upper3) + (105974019/100000000000000 : ℝ)*(upper5) + (671227955001179/25000000000000 : ℝ)*(major0) + (671227955001179/25000000000000 : ℝ)*(major1) + (671227955001179/25000000000000 : ℝ)*(major2) + (3899651781852249/100000000000000 : ℝ)*(sp0) + (389966436785609/10000000000000 : ℝ)*(sp1) + (3899664433950739/100000000000000 : ℝ)*(sp2) + (1470152392474107/100000000000000 : ℝ)*(sp3) + (13656498943/100000000000000 : ℝ)*(sp4) + (1117065083/20000000000000 : ℝ)*(sp7) + (735078988899761/50000000000000 : ℝ)*(f.failure) + (487458179793899/12500000000000 : ℝ)*(f.sum) + (92708321369453/27325000000000000000000000000 : ℝ)*base66 + (2556339067394017249/1366250000000000000000000000000000 : ℝ)*base67 + (3351369436465267249/1366250000000000000000000000000000 : ℝ)*base69 + (9179397121912232751/1366250000000000000000000000000000 : ℝ)*base72 + (99835713221097/27325000000000000000000000000 : ℝ)*base73 + (6064255351992767249/1366250000000000000000000000000000 : ℝ)*base75 + (25795810923350982751/1366250000000000000000000000000000 : ℝ)*base78 + (1743258904520267249/1366250000000000000000000000000000 : ℝ)*base79 + (10312756550317/1707812500000000000000000000 : ℝ)*base81 + (3110699/1250000000000000000000 : ℝ)*base89 + (3110699/1250000000000000000000 : ℝ)*base91 + (3110699/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9073212922830653238514597371/683125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1872714111/100000000000000 : ℝ)*(base19) + (82147307/4000000000000 : ℝ)*(base23) + (119013647/20000000000000 : ℝ)*(lower1) + (273615987/100000000000000 : ℝ)*(upper3) + (491749/625000000000 : ℝ)*(lower4) + (68879821/25000000000000 : ℝ)*(upper5) + (1363342885656053/50000000000000 : ℝ)*(major0) + (1363342885656053/50000000000000 : ℝ)*(major1) + (1363342885656053/50000000000000 : ℝ)*(major2) + (1524073497/100000000000000 : ℝ)*(sp2) + (198016962905517/5000000000000 : ℝ)*(sp4) + (3960337385396229/100000000000000 : ℝ)*(sp5) + (495041960044271/12500000000000 : ℝ)*(sp6) + (1493031841783129/100000000000000 : ℝ)*(sp7) + (1493031841783129/100000000000000 : ℝ)*(f.failure) + (198016962905517/5000000000000 : ℝ)*(f.sum) + (128608407978227/27325000000000000000000000000 : ℝ)*base65 + (12336066031188557457/2732500000000000000000000000000000 : ℝ)*base68 + (14168001840126442543/2732500000000000000000000000000000 : ℝ)*base69 + (103349077412386442543/2732500000000000000000000000000000 : ℝ)*base71 + (24645450603913/6831250000000000000000000000 : ℝ)*base73 + (9468620214503942543/2732500000000000000000000000000000 : ℝ)*base75 + (22921134390696442543/2732500000000000000000000000000000 : ℝ)*base77 + (6553912597681442543/2732500000000000000000000000000000 : ℝ)*base79 + (175666426043427/27325000000000000000000000000 : ℝ)*base81 + (20668189/2500000000000000000000 : ℝ)*base90 + (20668189/2500000000000000000000 : ℝ)*base92 + (20668189/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1670_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16231/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1670_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1670_s5_0 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336167503/2500000000 : ℝ)*x 0 + (-424014363/2500000000 : ℝ)*x 1 + (5185158033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336167503/2500000000 : ℝ)^4999 ≤ (11370265089063/25000000000000 : ℝ)^3975 := by
    have hnat : (1336167503 : ℕ)^4999*25000000000000^3975 ≤ 11370265089063^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336167503 2500000000 11370265089063 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424014363/2500000000 : ℝ)^4999 ≤ (429533147867/4000000000000 : ℝ)^3975 := by
    have hnat : (424014363 : ℕ)^4999*4000000000000^3975 ≤ 429533147867^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424014363 2500000000 429533147867 4000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185158033/10000000000 : ℝ)^4999 ≤ (21890305462741/50000000000000 : ℝ)^3975 := by
    have hnat : (5185158033 : ℕ)^4999*50000000000000^3975 ≤ 21890305462741^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185158033 10000000000 21890305462741 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336167503/2500000000 : ℝ), (-424014363/2500000000 : ℝ), (5185158033/10000000000 : ℝ)] ![(11370265089063/25000000000000 : ℝ), (429533147867/4000000000000 : ℝ), (21890305462741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336167503/2500000000 : ℝ)|^4999 ≤ (11370265089063/25000000000000 : ℝ)^3975
        have hw : |(1336167503/2500000000 : ℝ)|=(1336167503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424014363/2500000000 : ℝ)|^4999 ≤ (429533147867/4000000000000 : ℝ)^3975
        have hw : |(-424014363/2500000000 : ℝ)|=(424014363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185158033/10000000000 : ℝ)|^4999 ≤ (21890305462741/50000000000000 : ℝ)^3975
        have hw : |(5185158033/10000000000 : ℝ)|=(5185158033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s5_1 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-782111107/5000000000 : ℝ)*x 0 + (2593556741/5000000000 : ℝ)*x 1 + (2719800141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (782111107/5000000000 : ℝ)^4999 ≤ (9699327462603/100000000000000 : ℝ)^3975 := by
    have hnat : (782111107 : ℕ)^4999*100000000000000^3975 ≤ 9699327462603^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782111107 5000000000 9699327462603 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593556741/5000000000 : ℝ)^4999 ≤ (1095034399901/2500000000000 : ℝ)^3975 := by
    have hnat : (2593556741 : ℕ)^4999*2500000000000^3975 ≤ 1095034399901^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593556741 5000000000 1095034399901 2500000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719800141/5000000000 : ℝ)^4999 ≤ (46499296530627/100000000000000 : ℝ)^3975 := by
    have hnat : (2719800141 : ℕ)^4999*100000000000000^3975 ≤ 46499296530627^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719800141 5000000000 46499296530627 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-782111107/5000000000 : ℝ), (2593556741/5000000000 : ℝ), (2719800141/5000000000 : ℝ)] ![(9699327462603/100000000000000 : ℝ), (1095034399901/2500000000000 : ℝ), (46499296530627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-782111107/5000000000 : ℝ)|^4999 ≤ (9699327462603/100000000000000 : ℝ)^3975
        have hw : |(-782111107/5000000000 : ℝ)|=(782111107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593556741/5000000000 : ℝ)|^4999 ≤ (1095034399901/2500000000000 : ℝ)^3975
        have hw : |(2593556741/5000000000 : ℝ)|=(2593556741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719800141/5000000000 : ℝ)|^4999 ≤ (46499296530627/100000000000000 : ℝ)^3975
        have hw : |(2719800141/5000000000 : ℝ)|=(2719800141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s5_2 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276022781/10000000000 : ℝ)*x 0 + (-1441615041/10000000000 : ℝ)*x 1 + (5439600323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276022781/10000000000 : ℝ)^4999 ≤ (44747632619973/100000000000000 : ℝ)^3975 := by
    have hnat : (5276022781 : ℕ)^4999*100000000000000^3975 ≤ 44747632619973^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276022781 10000000000 44747632619973 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1441615041/10000000000 : ℝ)^4999 ≤ (4376535198949/50000000000000 : ℝ)^3975 := by
    have hnat : (1441615041 : ℕ)^4999*50000000000000^3975 ≤ 4376535198949^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441615041 10000000000 4376535198949 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439600323/10000000000 : ℝ)^4999 ≤ (23249648485697/50000000000000 : ℝ)^3975 := by
    have hnat : (5439600323 : ℕ)^4999*50000000000000^3975 ≤ 23249648485697^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439600323 10000000000 23249648485697 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276022781/10000000000 : ℝ), (-1441615041/10000000000 : ℝ), (5439600323/10000000000 : ℝ)] ![(44747632619973/100000000000000 : ℝ), (4376535198949/50000000000000 : ℝ), (23249648485697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276022781/10000000000 : ℝ)|^4999 ≤ (44747632619973/100000000000000 : ℝ)^3975
        have hw : |(5276022781/10000000000 : ℝ)|=(5276022781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1441615041/10000000000 : ℝ)|^4999 ≤ (4376535198949/50000000000000 : ℝ)^3975
        have hw : |(-1441615041/10000000000 : ℝ)|=(1441615041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439600323/10000000000 : ℝ)|^4999 ≤ (23249648485697/50000000000000 : ℝ)^3975
        have hw : |(5439600323/10000000000 : ℝ)|=(5439600323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s5_3 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276022873/10000000000 : ℝ)*x 0 + (679950023/1250000000 : ℝ)*x 1 + (-360403777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276022873/10000000000 : ℝ)^4999 ≤ (44747633601263/100000000000000 : ℝ)^3975 := by
    have hnat : (5276022873 : ℕ)^4999*100000000000000^3975 ≤ 44747633601263^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276022873 10000000000 44747633601263 100000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679950023/1250000000 : ℝ)^4999 ≤ (23249647738543/50000000000000 : ℝ)^3975 := by
    have hnat : (679950023 : ℕ)^4999*50000000000000^3975 ≤ 23249647738543^3975*1250000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679950023 1250000000 23249647738543 50000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360403777/2500000000 : ℝ)^4999 ≤ (17506141819/200000000000 : ℝ)^3975 := by
    have hnat : (360403777 : ℕ)^4999*200000000000^3975 ≤ 17506141819^3975*2500000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360403777 2500000000 17506141819 200000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276022873/10000000000 : ℝ), (679950023/1250000000 : ℝ), (-360403777/2500000000 : ℝ)] ![(44747633601263/100000000000000 : ℝ), (23249647738543/50000000000000 : ℝ), (17506141819/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276022873/10000000000 : ℝ)|^4999 ≤ (44747633601263/100000000000000 : ℝ)^3975
        have hw : |(5276022873/10000000000 : ℝ)|=(5276022873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679950023/1250000000 : ℝ)|^4999 ≤ (23249647738543/50000000000000 : ℝ)^3975
        have hw : |(679950023/1250000000 : ℝ)|=(679950023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-360403777/2500000000 : ℝ)|^4999 ≤ (17506141819/200000000000 : ℝ)^3975
        have hw : |(-360403777/2500000000 : ℝ)|=(360403777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1670_s5_4 (p : ℝ) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165840557/10000000000 : ℝ)*x 0 + (2255176273/5000000000 : ℝ)*x 1 + (3840619169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165840557/10000000000 : ℝ)^4999 ≤ (8311400816053/25000000000000 : ℝ)^3975 := by
    have hnat : (4165840557 : ℕ)^4999*25000000000000^3975 ≤ 8311400816053^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165840557 10000000000 8311400816053 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255176273/5000000000 : ℝ)^4999 ≤ (9184840952931/25000000000000 : ℝ)^3975 := by
    have hnat : (2255176273 : ℕ)^4999*25000000000000^3975 ≤ 9184840952931^3975*5000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255176273 5000000000 9184840952931 25000000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3840619169/10000000000 : ℝ)^4999 ≤ (75037582269/250000000000 : ℝ)^3975 := by
    have hnat : (3840619169 : ℕ)^4999*250000000000^3975 ≤ 75037582269^3975*10000000000^4999 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3840619169 10000000000 75037582269 250000000000 4999 3975 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4999/1024 : ℝ)) 4999 3975 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165840557/10000000000 : ℝ), (2255176273/5000000000 : ℝ), (3840619169/10000000000 : ℝ)] ![(8311400816053/25000000000000 : ℝ), (9184840952931/25000000000000 : ℝ), (75037582269/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165840557/10000000000 : ℝ)|^4999 ≤ (8311400816053/25000000000000 : ℝ)^3975
        have hw : |(4165840557/10000000000 : ℝ)|=(4165840557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255176273/5000000000 : ℝ)|^4999 ≤ (9184840952931/25000000000000 : ℝ)^3975
        have hw : |(2255176273/5000000000 : ℝ)|=(2255176273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3840619169/10000000000 : ℝ)|^4999 ≤ (75037582269/250000000000 : ℝ)^3975
        have hw : |(3840619169/10000000000 : ℝ)|=(3840619169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1670_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10769/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16227/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4057/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4057/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4057/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4057/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4057/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4057/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10769/100000 : ℝ) ^ (4995/1024 : ℝ) ≤ (1901163811698807/100000000000000000000 : ℝ) := by
    have hpowers : (10769/100000 : ℝ)^4995 ≤ (1901163811698807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10769 : ℕ)^4995*100000000000000000000^1024 ≤ 1901163811698807^1024*100000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10769 100000 1901163811698807 100000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10769/100000 : ℝ)) (X := (1901163811698807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4057/25000 : ℝ) ^ (4995/1024 : ℝ) ≤ (14051678139936699/100000000000000000000 : ℝ) := by
    have hpowers : (4057/25000 : ℝ)^4995 ≤ (14051678139936699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4057 : ℕ)^4995*100000000000000000000^1024 ≤ 14051678139936699^1024*25000^4995 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4057 25000 14051678139936699 100000000000000000000 4995 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4057/25000 : ℝ)) (X := (14051678139936699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001901163811698807/50000000000000000000 : ℝ) ≤ (10000077948441231/10000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (50001901163811698807/50000000000000000000 : ℝ)^1024 ≤ (10000077948441231/10000000000000000 : ℝ)^4995 := by
      have hnat : (50001901163811698807 : ℕ)^1024*10000000000000000^4995 ≤ 10000077948441231^4995*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001901163811698807 50000000000000000000 10000077948441231 10000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000077948441231/10000000000000000 : ℝ)) (X := (50001901163811698807/50000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007976420975817753/50000000000000000000 : ℝ) ≤ (5000163510254003/5000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (50007976420975817753/50000000000000000000 : ℝ)^1024 ≤ (5000163510254003/5000000000000000 : ℝ)^4995 := by
      have hnat : (50007976420975817753 : ℕ)^1024*5000000000000000^4995 ≤ 5000163510254003^4995*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007976420975817753 50000000000000000000 5000163510254003 5000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000163510254003/5000000000000000 : ℝ)) (X := (50007976420975817753/50000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014051678139936699/50000000000000000000 : ℝ) ≤ (10000576092574781/10000000000000000 : ℝ) ^ (4995/1024 : ℝ) := by
    have hpowers : (50014051678139936699/50000000000000000000 : ℝ)^1024 ≤ (10000576092574781/10000000000000000 : ℝ)^4995 := by
      have hnat : (50014051678139936699 : ℕ)^1024*10000000000000000^4995 ≤ 10000576092574781^4995*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014051678139936699 50000000000000000000 10000576092574781 10000000000000000 1024 4995 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000576092574781/10000000000000000 : ℝ)) (X := (50014051678139936699/50000000000000000000 : ℝ)) (by norm_num) 4995 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1901163811698807/100000000000000000000 : ℝ) ≤ ((54585061006366480079/54590000000000000000 : ℝ)+2*(9962882671/21836000000000 : ℝ)*(10769/100000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (54585061006366480079/54590000000000000000 : ℝ)+2*(9962882671/21836000000000 : ℝ)*(10769/100000 : ℝ)=(10000077948441231/10000000000000000 : ℝ) by norm_num, show 1+2*(1901163811698807/100000000000000000000 : ℝ)=(50001901163811698807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14051678139936699/100000000000000000000 : ℝ)+(1901163811698807/100000000000000000000 : ℝ) ≤ ((54585061006366480079/54590000000000000000 : ℝ)+(9962882671/21836000000000 : ℝ)*((4057/25000 : ℝ)+(10769/100000 : ℝ)))^(4995/1024 : ℝ) := by
    rw [show (54585061006366480079/54590000000000000000 : ℝ)+(9962882671/21836000000000 : ℝ)*((4057/25000 : ℝ)+(10769/100000 : ℝ))=(5000163510254003/5000000000000000 : ℝ) by norm_num, show 1+(14051678139936699/100000000000000000000 : ℝ)+(1901163811698807/100000000000000000000 : ℝ)=(50007976420975817753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14051678139936699/100000000000000000000 : ℝ) ≤ ((54585061006366480079/54590000000000000000 : ℝ)+2*(9962882671/21836000000000 : ℝ)*(4057/25000 : ℝ))^(4995/1024 : ℝ) := by
    rw [show (54585061006366480079/54590000000000000000 : ℝ)+2*(9962882671/21836000000000 : ℝ)*(4057/25000 : ℝ)=(10000576092574781/10000000000000000 : ℝ) by norm_num, show 1+2*(14051678139936699/100000000000000000000 : ℝ)=(50014051678139936699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54585061006366480079/54590000000000000000 : ℝ)*(X 1 0+X 2 0)+(9962882671/21836000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (54585061006366480079/54590000000000000000 : ℝ)) (alpha := (9962882671/21836000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54585061006366480079/54590000000000000000 : ℝ)*(X 0 1+X 2 1)+(9962882671/21836000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (54585061006366480079/54590000000000000000 : ℝ)) (alpha := (9962882671/21836000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54585061006366480079/54590000000000000000 : ℝ)*(X 0 2+X 1 2)+(9962882671/21836000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4995/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (54585061006366480079/54590000000000000000 : ℝ)) (alpha := (9962882671/21836000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336167503/2500000000 : ℝ)*X 1 0+(-424014363/2500000000 : ℝ)*X 1 1+(5185158033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s5_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-782111107/5000000000 : ℝ)*X 0 0+(2593556741/5000000000 : ℝ)*X 0 1+(2719800141/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5276022781/10000000000 : ℝ)*X 1 0+(-1441615041/10000000000 : ℝ)*X 1 1+(5439600323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5276022873/10000000000 : ℝ)*X 2 0+(679950023/1250000000 : ℝ)*X 2 1+(-360403777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4165840557/10000000000 : ℝ)*X 0 0+(2255176273/5000000000 : ℝ)*X 0 1+(3840619169/10000000000 : ℝ)*X 0 2+(4165840557/10000000000 : ℝ)*X 1 0+(2255176273/5000000000 : ℝ)*X 1 1+(3840619169/10000000000 : ℝ)*X 1 2+(4165840557/10000000000 : ℝ)*X 2 0+(2255176273/5000000000 : ℝ)*X 2 1+(3840619169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1670_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2644534319713450190541859629/682375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (471439821/100000000000000 : ℝ)*(base19) + (107351583/20000000000000 : ℝ)*(base23) + (3270909/2500000000000 : ℝ)*(lower1) + (5990103/100000000000000 : ℝ)*(upper2) + (35436369/50000000000000 : ℝ)*(upper3) + (22401477/25000000000000 : ℝ)*(upper5) + (1363432014678817/50000000000000 : ℝ)*(major0) + (1363432014678817/50000000000000 : ℝ)*(major1) + (1363432014678817/50000000000000 : ℝ)*(major2) + (1160371469/100000000000000 : ℝ)*(sp0) + (3960598480265201/100000000000000 : ℝ)*(sp1) + (3960596848453911/100000000000000 : ℝ)*(sp2) + (1980298971753643/50000000000000 : ℝ)*(sp3) + (746564724633607/50000000000000 : ℝ)*(sp4) + (746564724633607/50000000000000 : ℝ)*(f.failure) + (3960598480265201/100000000000000 : ℝ)*(f.sum) + (13945909220307/2729500000000000000000000000 : ℝ)*base65 + (40347074954085713457/2729500000000000000000000000000000 : ℝ)*base68 + (21831907814584713457/2729500000000000000000000000000000 : ℝ)*base70 + (10698879084720213457/2729500000000000000000000000000000 : ℝ)*base72 + (571047187229/218360000000000000000000000 : ℝ)*base74 + (1966092137899286543/2729500000000000000000000000000000 : ℝ)*base75 + (12251742291510713457/2729500000000000000000000000000000 : ℝ)*base78 + (11655664779374713457/2729500000000000000000000000000000 : ℝ)*base80 + (27268247711883/1364750000000000000000000000 : ℝ)*base82 + (3539587/1250000000000000000000 : ℝ)*base90 + (3539587/1250000000000000000000 : ℝ)*base92 + (3539587/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1670_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16227/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1670_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1670_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16227/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1670_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1670_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1670_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4995/1024 : ℝ) ≤ p) (hpb : p ≤ (4999/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45656859/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16227/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1670_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
