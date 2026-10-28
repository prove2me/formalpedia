-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:24:40.201099+00:00
-- url     : https://prove2.me/submissions/82a0a25d-c06b-4f57-9e71-e1068ad88da8

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
theorem support_rectangle_w1253_s6_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057445969/5000000000 : ℝ)*x 0 + (2695587171/5000000000 : ℝ)*x 1 + (131679713/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057445969/5000000000 : ℝ)^4223 ≤ (3215532594549/25000000000000 : ℝ)^3199 := by
    have hnat : (1057445969 : ℕ)^4223*25000000000000^3199 ≤ 3215532594549^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057445969 5000000000 3215532594549 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695587171/5000000000 : ℝ)^4223 ≤ (22118986379817/50000000000000 : ℝ)^3199 := by
    have hnat : (2695587171 : ℕ)^4223*50000000000000^3199 ≤ 22118986379817^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695587171 5000000000 22118986379817 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131679713/250000000 : ℝ)^4223 ≤ (42899896841411/100000000000000 : ℝ)^3199 := by
    have hnat : (131679713 : ℕ)^4223*100000000000000^3199 ≤ 42899896841411^3199*250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131679713 250000000 42899896841411 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057445969/5000000000 : ℝ), (2695587171/5000000000 : ℝ), (131679713/250000000 : ℝ)] ![(3215532594549/25000000000000 : ℝ), (22118986379817/50000000000000 : ℝ), (42899896841411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057445969/5000000000 : ℝ)|^4223 ≤ (3215532594549/25000000000000 : ℝ)^3199
        have hw : |(-1057445969/5000000000 : ℝ)|=(1057445969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695587171/5000000000 : ℝ)|^4223 ≤ (22118986379817/50000000000000 : ℝ)^3199
        have hw : |(2695587171/5000000000 : ℝ)|=(2695587171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131679713/250000000 : ℝ)|^4223 ≤ (42899896841411/100000000000000 : ℝ)^3199
        have hw : |(131679713/250000000 : ℝ)|=(131679713/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672148227/5000000000 : ℝ)*x 0 + (-2177755887/10000000000 : ℝ)*x 1 + (1053437703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672148227/5000000000 : ℝ)^4223 ≤ (43730887833763/100000000000000 : ℝ)^3199 := by
    have hnat : (2672148227 : ℕ)^4223*100000000000000^3199 ≤ 43730887833763^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672148227 5000000000 43730887833763 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177755887/10000000000 : ℝ)^4223 ≤ (3342303841943/25000000000000 : ℝ)^3199 := by
    have hnat : (2177755887 : ℕ)^4223*25000000000000^3199 ≤ 3342303841943^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177755887 10000000000 3342303841943 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053437703/2000000000 : ℝ)^4223 ≤ (42899896787651/100000000000000 : ℝ)^3199 := by
    have hnat : (1053437703 : ℕ)^4223*100000000000000^3199 ≤ 42899896787651^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053437703 2000000000 42899896787651 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672148227/5000000000 : ℝ), (-2177755887/10000000000 : ℝ), (1053437703/2000000000 : ℝ)] ![(43730887833763/100000000000000 : ℝ), (3342303841943/25000000000000 : ℝ), (42899896787651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672148227/5000000000 : ℝ)|^4223 ≤ (43730887833763/100000000000000 : ℝ)^3199
        have hw : |(2672148227/5000000000 : ℝ)|=(2672148227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177755887/10000000000 : ℝ)|^4223 ≤ (3342303841943/25000000000000 : ℝ)^3199
        have hw : |(-2177755887/10000000000 : ℝ)|=(2177755887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053437703/2000000000 : ℝ)|^4223 ≤ (42899896787651/100000000000000 : ℝ)^3199
        have hw : |(1053437703/2000000000 : ℝ)|=(1053437703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344296461/10000000000 : ℝ)*x 0 + (1053437703/2000000000 : ℝ)*x 1 + (-1088877939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344296461/10000000000 : ℝ)^4223 ≤ (43730887909377/100000000000000 : ℝ)^3199 := by
    have hnat : (5344296461 : ℕ)^4223*100000000000000^3199 ≤ 43730887909377^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344296461 10000000000 43730887909377 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053437703/2000000000 : ℝ)^4223 ≤ (42899896787651/100000000000000 : ℝ)^3199 := by
    have hnat : (1053437703 : ℕ)^4223*100000000000000^3199 ≤ 42899896787651^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053437703 2000000000 42899896787651 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088877939/5000000000 : ℝ)^4223 ≤ (2673843058967/20000000000000 : ℝ)^3199 := by
    have hnat : (1088877939 : ℕ)^4223*20000000000000^3199 ≤ 2673843058967^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088877939 5000000000 2673843058967 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344296461/10000000000 : ℝ), (1053437703/2000000000 : ℝ), (-1088877939/5000000000 : ℝ)] ![(43730887909377/100000000000000 : ℝ), (42899896787651/100000000000000 : ℝ), (2673843058967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344296461/10000000000 : ℝ)|^4223 ≤ (43730887909377/100000000000000 : ℝ)^3199
        have hw : |(5344296461/10000000000 : ℝ)|=(5344296461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053437703/2000000000 : ℝ)|^4223 ≤ (42899896787651/100000000000000 : ℝ)^3199
        have hw : |(1053437703/2000000000 : ℝ)|=(1053437703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088877939/5000000000 : ℝ)|^4223 ≤ (2673843058967/20000000000000 : ℝ)^3199
        have hw : |(-1088877939/5000000000 : ℝ)|=(1088877939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087314447/2500000000 : ℝ)*x 0 + (4225004311/10000000000 : ℝ)*x 1 + (1119263157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087314447/2500000000 : ℝ)^4223 ≤ (33317455624921/100000000000000 : ℝ)^3199 := by
    have hnat : (1087314447 : ℕ)^4223*100000000000000^3199 ≤ 33317455624921^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087314447 2500000000 33317455624921 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225004311/10000000000 : ℝ)^4223 ≤ (6413342196277/20000000000000 : ℝ)^3199 := by
    have hnat : (4225004311 : ℕ)^4223*20000000000000^3199 ≤ 6413342196277^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225004311 10000000000 6413342196277 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119263157/2500000000 : ℝ)^4223 ≤ (270436198269/781250000000 : ℝ)^3199 := by
    have hnat : (1119263157 : ℕ)^4223*781250000000^3199 ≤ 270436198269^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119263157 2500000000 270436198269 781250000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087314447/2500000000 : ℝ), (4225004311/10000000000 : ℝ), (1119263157/2500000000 : ℝ)] ![(33317455624921/100000000000000 : ℝ), (6413342196277/20000000000000 : ℝ), (270436198269/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087314447/2500000000 : ℝ)|^4223 ≤ (33317455624921/100000000000000 : ℝ)^3199
        have hw : |(1087314447/2500000000 : ℝ)|=(1087314447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225004311/10000000000 : ℝ)|^4223 ≤ (6413342196277/20000000000000 : ℝ)^3199
        have hw : |(4225004311/10000000000 : ℝ)|=(4225004311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119263157/2500000000 : ℝ)|^4223 ≤ (270436198269/781250000000 : ℝ)^3199
        have hw : |(1119263157/2500000000 : ℝ)|=(1119263157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057448487/5000000000 : ℝ)*x 0 + (2633750861/5000000000 : ℝ)*x 1 + (2695429863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057448487/5000000000 : ℝ)^4223 ≤ (12862170809473/100000000000000 : ℝ)^3199 := by
    have hnat : (1057448487 : ℕ)^4223*100000000000000^3199 ≤ 12862170809473^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057448487 5000000000 12862170809473 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633750861/5000000000 : ℝ)^4223 ≤ (42903264382367/100000000000000 : ℝ)^3199 := by
    have hnat : (2633750861 : ℕ)^4223*100000000000000^3199 ≤ 42903264382367^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633750861 5000000000 42903264382367 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695429863/5000000000 : ℝ)^4223 ≤ (11058641198061/25000000000000 : ℝ)^3199 := by
    have hnat : (2695429863 : ℕ)^4223*25000000000000^3199 ≤ 11058641198061^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695429863 5000000000 11058641198061 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057448487/5000000000 : ℝ), (2633750861/5000000000 : ℝ), (2695429863/5000000000 : ℝ)] ![(12862170809473/100000000000000 : ℝ), (42903264382367/100000000000000 : ℝ), (11058641198061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057448487/5000000000 : ℝ)|^4223 ≤ (12862170809473/100000000000000 : ℝ)^3199
        have hw : |(-1057448487/5000000000 : ℝ)|=(1057448487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633750861/5000000000 : ℝ)|^4223 ≤ (42903264382367/100000000000000 : ℝ)^3199
        have hw : |(2633750861/5000000000 : ℝ)|=(2633750861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695429863/5000000000 : ℝ)|^4223 ≤ (11058641198061/25000000000000 : ℝ)^3199
        have hw : |(2695429863/5000000000 : ℝ)|=(2695429863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212505521/400000000 : ℝ)*x 0 + (-513521151/2500000000 : ℝ)*x 1 + (2695429593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212505521/400000000 : ℝ)^4223 ≤ (21694618907119/50000000000000 : ℝ)^3199 := by
    have hnat : (212505521 : ℕ)^4223*50000000000000^3199 ≤ 21694618907119^3199*400000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212505521 400000000 21694618907119 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513521151/2500000000 : ℝ)^4223 ≤ (3094050809191/25000000000000 : ℝ)^3199 := by
    have hnat : (513521151 : ℕ)^4223*25000000000000^3199 ≤ 3094050809191^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513521151 2500000000 3094050809191 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695429593/5000000000 : ℝ)^4223 ≤ (44234558942939/100000000000000 : ℝ)^3199 := by
    have hnat : (2695429593 : ℕ)^4223*100000000000000^3199 ≤ 44234558942939^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695429593 5000000000 44234558942939 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212505521/400000000 : ℝ), (-513521151/2500000000 : ℝ), (2695429593/5000000000 : ℝ)] ![(21694618907119/50000000000000 : ℝ), (3094050809191/25000000000000 : ℝ), (44234558942939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212505521/400000000 : ℝ)|^4223 ≤ (21694618907119/50000000000000 : ℝ)^3199
        have hw : |(212505521/400000000 : ℝ)|=(212505521/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513521151/2500000000 : ℝ)|^4223 ≤ (3094050809191/25000000000000 : ℝ)^3199
        have hw : |(-513521151/2500000000 : ℝ)|=(513521151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695429593/5000000000 : ℝ)|^4223 ≤ (44234558942939/100000000000000 : ℝ)^3199
        have hw : |(2695429593/5000000000 : ℝ)|=(2695429593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328159569/2500000000 : ℝ)*x 0 + (5390858761/10000000000 : ℝ)*x 1 + (-2054084843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328159569/2500000000 : ℝ)^4223 ≤ (43389240520391/100000000000000 : ℝ)^3199 := by
    have hnat : (1328159569 : ℕ)^4223*100000000000000^3199 ≤ 43389240520391^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328159569 2500000000 43389240520391 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390858761/10000000000 : ℝ)^4223 ≤ (22117277169659/50000000000000 : ℝ)^3199 := by
    have hnat : (5390858761 : ℕ)^4223*50000000000000^3199 ≤ 22117277169659^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390858761 10000000000 22117277169659 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054084843/10000000000 : ℝ)^4223 ≤ (193378205277/1562500000000 : ℝ)^3199 := by
    have hnat : (2054084843 : ℕ)^4223*1562500000000^3199 ≤ 193378205277^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054084843 10000000000 193378205277 1562500000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328159569/2500000000 : ℝ), (5390858761/10000000000 : ℝ), (-2054084843/10000000000 : ℝ)] ![(43389240520391/100000000000000 : ℝ), (22117277169659/50000000000000 : ℝ), (193378205277/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328159569/2500000000 : ℝ)|^4223 ≤ (43389240520391/100000000000000 : ℝ)^3199
        have hw : |(1328159569/2500000000 : ℝ)|=(1328159569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390858761/10000000000 : ℝ)|^4223 ≤ (22117277169659/50000000000000 : ℝ)^3199
        have hw : |(5390858761/10000000000 : ℝ)|=(5390858761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054084843/10000000000 : ℝ)|^4223 ≤ (193378205277/1562500000000 : ℝ)^3199
        have hw : |(-2054084843/10000000000 : ℝ)|=(2054084843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434926727/1000000000 : ℝ)*x 0 + (4476415009/10000000000 : ℝ)*x 1 + (4225644267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434926727/1000000000 : ℝ)^4223 ≤ (1665877575639/5000000000000 : ℝ)^3199 := by
    have hnat : (434926727 : ℕ)^4223*5000000000000^3199 ≤ 1665877575639^3199*1000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434926727 1000000000 1665877575639 5000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476415009/10000000000 : ℝ)^4223 ≤ (34609325479743/100000000000000 : ℝ)^3199 := by
    have hnat : (4476415009 : ℕ)^4223*100000000000000^3199 ≤ 34609325479743^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476415009 10000000000 34609325479743 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225644267/10000000000 : ℝ)^4223 ≤ (32073122999573/100000000000000 : ℝ)^3199 := by
    have hnat : (4225644267 : ℕ)^4223*100000000000000^3199 ≤ 32073122999573^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225644267 10000000000 32073122999573 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434926727/1000000000 : ℝ), (4476415009/10000000000 : ℝ), (4225644267/10000000000 : ℝ)] ![(1665877575639/5000000000000 : ℝ), (34609325479743/100000000000000 : ℝ), (32073122999573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434926727/1000000000 : ℝ)|^4223 ≤ (1665877575639/5000000000000 : ℝ)^3199
        have hw : |(434926727/1000000000 : ℝ)|=(434926727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476415009/10000000000 : ℝ)|^4223 ≤ (34609325479743/100000000000000 : ℝ)^3199
        have hw : |(4476415009/10000000000 : ℝ)|=(4476415009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225644267/10000000000 : ℝ)|^4223 ≤ (32073122999573/100000000000000 : ℝ)^3199
        have hw : |(4225644267/10000000000 : ℝ)|=(4225644267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s6_8 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38205959/10000000000 : ℝ)*x 0 + (5912217617/10000000000 : ℝ)*x 1 + (2956139519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38205959/10000000000 : ℝ)^4223 ≤ (514352889/800000000000 : ℝ)^3199 := by
    have hnat : (38205959 : ℕ)^4223*800000000000^3199 ≤ 514352889^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38205959 10000000000 514352889 800000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5912217617/10000000000 : ℝ)^4223 ≤ (9993502060641/20000000000000 : ℝ)^3199 := by
    have hnat : (5912217617 : ℕ)^4223*20000000000000^3199 ≤ 9993502060641^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912217617 10000000000 9993502060641 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956139519/5000000000 : ℝ)^4223 ≤ (24984097786623/50000000000000 : ℝ)^3199 := by
    have hnat : (2956139519 : ℕ)^4223*50000000000000^3199 ≤ 24984097786623^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956139519 5000000000 24984097786623 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38205959/10000000000 : ℝ), (5912217617/10000000000 : ℝ), (2956139519/5000000000 : ℝ)] ![(514352889/800000000000 : ℝ), (9993502060641/20000000000000 : ℝ), (24984097786623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38205959/10000000000 : ℝ)|^4223 ≤ (514352889/800000000000 : ℝ)^3199
        have hw : |(-38205959/10000000000 : ℝ)|=(38205959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5912217617/10000000000 : ℝ)|^4223 ≤ (9993502060641/20000000000000 : ℝ)^3199
        have hw : |(5912217617/10000000000 : ℝ)|=(5912217617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956139519/5000000000 : ℝ)|^4223 ≤ (24984097786623/50000000000000 : ℝ)^3199
        have hw : |(2956139519/5000000000 : ℝ)|=(2956139519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (359/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2827/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2867/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2827/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2867/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2827/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2867/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2827/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2867/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2827/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2867/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2827/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2867/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2867/25000 : ℝ) ^ (8445/2048 : ℝ) ≤ (2647246585942021/20000000000000000000 : ℝ) := by
    have hpowers : (2867/25000 : ℝ)^8445 ≤ (2647246585942021/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2867 : ℕ)^8445*20000000000000000000^2048 ≤ 2647246585942021^2048*25000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2867 25000 2647246585942021 20000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2867/25000 : ℝ)) (X := (2647246585942021/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2827/20000 : ℝ) ^ (8445/2048 : ℝ) ≤ (7837091556866707/25000000000000000000 : ℝ) := by
    have hpowers : (2827/20000 : ℝ)^8445 ≤ (7837091556866707/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2827 : ℕ)^8445*25000000000000000000^2048 ≤ 7837091556866707^2048*20000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 20000 7837091556866707 25000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/20000 : ℝ)) (X := (7837091556866707/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002647246585942021/10000000000000000000 : ℝ) ≤ (2500160480092061/2500000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (10002647246585942021/10000000000000000000 : ℝ)^2048 ≤ (2500160480092061/2500000000000000 : ℝ)^8445 := by
      have hnat : (10002647246585942021 : ℕ)^2048*2500000000000000^8445 ≤ 2500160480092061^8445*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002647246585942021 10000000000000000000 2500160480092061 2500000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500160480092061/2500000000000000 : ℝ)) (X := (10002647246585942021/10000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044584599157176933/100000000000000000000 : ℝ) ≤ (10001081040194773/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (100044584599157176933/100000000000000000000 : ℝ)^2048 ≤ (10001081040194773/10000000000000000 : ℝ)^8445 := by
      have hnat : (100044584599157176933 : ℕ)^2048*10000000000000000^8445 ≤ 10001081040194773^8445*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044584599157176933 100000000000000000000 10001081040194773 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001081040194773/10000000000000000 : ℝ)) (X := (100044584599157176933/100000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507837091556866707/12500000000000000000 : ℝ) ≤ (5000760080010651/5000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (12507837091556866707/12500000000000000000 : ℝ)^2048 ≤ (5000760080010651/5000000000000000 : ℝ)^8445 := by
      have hnat : (12507837091556866707 : ℕ)^2048*5000000000000000^8445 ≤ 5000760080010651^8445*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507837091556866707 12500000000000000000 5000760080010651 5000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000760080010651/5000000000000000 : ℝ)) (X := (12507837091556866707/12500000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2647246585942021/20000000000000000000 : ℝ) ≤ ((6665410087320209401/6667500000000000000 : ℝ)+2*(439119826529/266700000000000 : ℝ)*(2867/25000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (6665410087320209401/6667500000000000000 : ℝ)+2*(439119826529/266700000000000 : ℝ)*(2867/25000 : ℝ)=(2500160480092061/2500000000000000 : ℝ) by norm_num, show 1+2*(2647246585942021/20000000000000000000 : ℝ)=(10002647246585942021/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7837091556866707/25000000000000000000 : ℝ)+(2647246585942021/20000000000000000000 : ℝ) ≤ ((6665410087320209401/6667500000000000000 : ℝ)+(439119826529/266700000000000 : ℝ)*((2827/20000 : ℝ)+(2867/25000 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (6665410087320209401/6667500000000000000 : ℝ)+(439119826529/266700000000000 : ℝ)*((2827/20000 : ℝ)+(2867/25000 : ℝ))=(10001081040194773/10000000000000000 : ℝ) by norm_num, show 1+(7837091556866707/25000000000000000000 : ℝ)+(2647246585942021/20000000000000000000 : ℝ)=(100044584599157176933/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7837091556866707/25000000000000000000 : ℝ) ≤ ((6665410087320209401/6667500000000000000 : ℝ)+2*(439119826529/266700000000000 : ℝ)*(2827/20000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (6665410087320209401/6667500000000000000 : ℝ)+2*(439119826529/266700000000000 : ℝ)*(2827/20000 : ℝ)=(5000760080010651/5000000000000000 : ℝ) by norm_num, show 1+2*(7837091556866707/25000000000000000000 : ℝ)=(12507837091556866707/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6665410087320209401/6667500000000000000 : ℝ)*(X 1 0+X 2 0)+(439119826529/266700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (2867/25000 : ℝ)) (hi := (2827/20000 : ℝ)) (c := (6665410087320209401/6667500000000000000 : ℝ)) (alpha := (439119826529/266700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6665410087320209401/6667500000000000000 : ℝ)*(X 0 1+X 2 1)+(439119826529/266700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (2867/25000 : ℝ)) (hi := (2827/20000 : ℝ)) (c := (6665410087320209401/6667500000000000000 : ℝ)) (alpha := (439119826529/266700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6665410087320209401/6667500000000000000 : ℝ)*(X 0 2+X 1 2)+(439119826529/266700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (2867/25000 : ℝ)) (hi := (2827/20000 : ℝ)) (c := (6665410087320209401/6667500000000000000 : ℝ)) (alpha := (439119826529/266700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1057445969/5000000000 : ℝ)*X 0 0+(2695587171/5000000000 : ℝ)*X 0 1+(131679713/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672148227/5000000000 : ℝ)*X 1 0+(-2177755887/10000000000 : ℝ)*X 1 1+(1053437703/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344296461/10000000000 : ℝ)*X 2 0+(1053437703/2000000000 : ℝ)*X 2 1+(-1088877939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087314447/2500000000 : ℝ)*X 0 0+(4225004311/10000000000 : ℝ)*X 0 1+(1119263157/2500000000 : ℝ)*X 0 2+(1087314447/2500000000 : ℝ)*X 1 0+(4225004311/10000000000 : ℝ)*X 1 1+(1119263157/2500000000 : ℝ)*X 1 2+(1087314447/2500000000 : ℝ)*X 2 0+(4225004311/10000000000 : ℝ)*X 2 1+(1119263157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1057448487/5000000000 : ℝ)*X 0 0+(2633750861/5000000000 : ℝ)*X 0 1+(2695429863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212505521/400000000 : ℝ)*X 1 0+(-513521151/2500000000 : ℝ)*X 1 1+(2695429593/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328159569/2500000000 : ℝ)*X 2 0+(5390858761/10000000000 : ℝ)*X 2 1+(-2054084843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434926727/1000000000 : ℝ)*X 0 0+(4476415009/10000000000 : ℝ)*X 0 1+(4225644267/10000000000 : ℝ)*X 0 2+(434926727/1000000000 : ℝ)*X 1 0+(4476415009/10000000000 : ℝ)*X 1 1+(4225644267/10000000000 : ℝ)*X 1 2+(434926727/1000000000 : ℝ)*X 2 0+(4476415009/10000000000 : ℝ)*X 2 1+(4225644267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-38205959/10000000000 : ℝ)*X 0 0+(5912217617/10000000000 : ℝ)*X 0 1+(2956139519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12448209066500398007079/2222500000000000000000000000 : ℝ) := by norm_num
    linear_combination (59237101/20000000000000 : ℝ)*(lower2) + (56554233/50000000000000 : ℝ)*(lower3) + (1174717/400000000000 : ℝ)*(lower4) + (76877727/100000000000000 : ℝ)*(lower5) + (6016466570383491/100000000000000 : ℝ)*(major0) + (6016466570383491/100000000000000 : ℝ)*(major1) + (6016466570383491/100000000000000 : ℝ)*(major2) + (8065436389180049/100000000000000 : ℝ)*(sp0) + (252044815257013/3125000000000 : ℝ)*(sp1) + (4032716548242359/50000000000000 : ℝ)*(sp2) + (1983746963623227/50000000000000 : ℝ)*(sp3) + (4938596297/100000000000000 : ℝ)*(sp5) + (1186067199/20000000000000 : ℝ)*(sp6) + (329705083/12500000000000 : ℝ)*(sp8) + (1983746963623227/50000000000000 : ℝ)*(f.failure) + (1008179878352589/12500000000000 : ℝ)*(f.sum) + (66424027958683/4445000000000000000000000000 : ℝ)*base65 + (1607189600947291297/222250000000000000000000000000000 : ℝ)*base67 + (2993757930946708703/222250000000000000000000000000000 : ℝ)*base70 + (14819828885325041297/222250000000000000000000000000000 : ℝ)*base71 + (13882381962683/4445000000000000000000000000 : ℝ)*base73 + (3099632890329208703/222250000000000000000000000000000 : ℝ)*base76 + (3846432197954791297/222250000000000000000000000000000 : ℝ)*base77 + (668324918150458703/222250000000000000000000000000000 : ℝ)*base80 + (5726216664089/2222500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6217227/2500000000000000000000 : ℝ)*base89 + (6217227/2500000000000000000000 : ℝ)*base91 + (6217227/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (160144101811166231346921937/111125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200008551/25000000000000 : ℝ)*(lower2) + (179505009/100000000000000 : ℝ)*(lower3) + (298279449/50000000000000 : ℝ)*(lower4) + (761150917/100000000000000 : ℝ)*(lower5) + (6047160245513621/100000000000000 : ℝ)*(major0) + (6047160245513621/100000000000000 : ℝ)*(major1) + (6047160245513621/100000000000000 : ℝ)*(major2) + (13773290441/25000000000000 : ℝ)*(sp0) + (50815011/781250000000 : ℝ)*(sp3) + (810652269562089/10000000000000 : ℝ)*(sp4) + (8106585903041881/100000000000000 : ℝ)*(sp5) + (8106585903041881/100000000000000 : ℝ)*(sp6) + (1993864017813357/50000000000000 : ℝ)*(sp7) + (4057129613/50000000000000 : ℝ)*(sp8) + (1993867269974061/50000000000000 : ℝ)*(f.failure) + (8106585903041881/100000000000000 : ℝ)*(f.sum) + (421324806873079/13335000000000000000000000000 : ℝ)*base65 + (3512758364584492007/222250000000000000000000000000000 : ℝ)*base67 + (1836819510410992007/222250000000000000000000000000000 : ℝ)*base69 + (4288912108343242007/222250000000000000000000000000000 : ℝ)*base71 + (50251961282141/13335000000000000000000000000 : ℝ)*base74 + (1293498524220492007/222250000000000000000000000000000 : ℝ)*base75 + (3919196537228492007/222250000000000000000000000000000 : ℝ)*base77 + (2577007381219742007/222250000000000000000000000000000 : ℝ)*base79 + (5917547987557/1666875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1883939/2500000000000000000000 : ℝ)*base90 + (1883939/2500000000000000000000 : ℝ)*base92 + (1883939/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1253_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (359/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1253_s7_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-211490783/1000000000 : ℝ)*x 0 + (5390983509/10000000000 : ℝ)*x 1 + (5267368911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211490783/1000000000 : ℝ)^4223 ≤ (3215564491609/25000000000000 : ℝ)^3199 := by
    have hnat : (211490783 : ℕ)^4223*25000000000000^3199 ≤ 3215564491609^3199*1000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211490783 1000000000 3215564491609 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390983509/10000000000 : ℝ)^4223 ≤ (11058976405137/25000000000000 : ℝ)^3199 := by
    have hnat : (5390983509 : ℕ)^4223*25000000000000^3199 ≤ 11058976405137^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390983509 10000000000 11058976405137 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267368911/10000000000 : ℝ)^4223 ≤ (21450918196807/50000000000000 : ℝ)^3199 := by
    have hnat : (5267368911 : ℕ)^4223*50000000000000^3199 ≤ 21450918196807^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267368911 10000000000 21450918196807 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211490783/1000000000 : ℝ), (5390983509/10000000000 : ℝ), (5267368911/10000000000 : ℝ)] ![(3215564491609/25000000000000 : ℝ), (11058976405137/25000000000000 : ℝ), (21450918196807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211490783/1000000000 : ℝ)|^4223 ≤ (3215564491609/25000000000000 : ℝ)^3199
        have hw : |(-211490783/1000000000 : ℝ)|=(211490783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390983509/10000000000 : ℝ)|^4223 ≤ (11058976405137/25000000000000 : ℝ)^3199
        have hw : |(5390983509/10000000000 : ℝ)|=(5390983509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267368911/10000000000 : ℝ)|^4223 ≤ (21450918196807/50000000000000 : ℝ)^3199
        have hw : |(5267368911/10000000000 : ℝ)|=(5267368911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s7_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344247809/10000000000 : ℝ)*x 0 + (-1088790469/5000000000 : ℝ)*x 1 + (5267369249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344247809/10000000000 : ℝ)^4223 ≤ (5466295296341/12500000000000 : ℝ)^3199 := by
    have hnat : (5344247809 : ℕ)^4223*12500000000000^3199 ≤ 5466295296341^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344247809 10000000000 5466295296341 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088790469/5000000000 : ℝ)^4223 ≤ (1670974698227/12500000000000 : ℝ)^3199 := by
    have hnat : (1088790469 : ℕ)^4223*12500000000000^3199 ≤ 1670974698227^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088790469 5000000000 1670974698227 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267369249/10000000000 : ℝ)^4223 ≤ (10725460006947/25000000000000 : ℝ)^3199 := by
    have hnat : (5267369249 : ℕ)^4223*25000000000000^3199 ≤ 10725460006947^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267369249 10000000000 10725460006947 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344247809/10000000000 : ℝ), (-1088790469/5000000000 : ℝ), (5267369249/10000000000 : ℝ)] ![(5466295296341/12500000000000 : ℝ), (1670974698227/12500000000000 : ℝ), (10725460006947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344247809/10000000000 : ℝ)|^4223 ≤ (5466295296341/12500000000000 : ℝ)^3199
        have hw : |(5344247809/10000000000 : ℝ)|=(5344247809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088790469/5000000000 : ℝ)|^4223 ≤ (1670974698227/12500000000000 : ℝ)^3199
        have hw : |(-1088790469/5000000000 : ℝ)|=(1088790469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267369249/10000000000 : ℝ)|^4223 ≤ (10725460006947/25000000000000 : ℝ)^3199
        have hw : |(5267369249/10000000000 : ℝ)|=(5267369249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s7_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344247643/10000000000 : ℝ)*x 0 + (5267369321/10000000000 : ℝ)*x 1 + (-272197633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344247643/10000000000 : ℝ)^4223 ≤ (43730360577599/100000000000000 : ℝ)^3199 := by
    have hnat : (5344247643 : ℕ)^4223*100000000000000^3199 ≤ 43730360577599^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344247643 10000000000 43730360577599 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267369321/10000000000 : ℝ)^4223 ≤ (42901840801931/100000000000000 : ℝ)^3199 := by
    have hnat : (5267369321 : ℕ)^4223*100000000000000^3199 ≤ 42901840801931^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267369321 10000000000 42901840801931 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272197633/1250000000 : ℝ)^4223 ≤ (1670974825863/12500000000000 : ℝ)^3199 := by
    have hnat : (272197633 : ℕ)^4223*12500000000000^3199 ≤ 1670974825863^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272197633 1250000000 1670974825863 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344247643/10000000000 : ℝ), (5267369321/10000000000 : ℝ), (-272197633/1250000000 : ℝ)] ![(43730360577599/100000000000000 : ℝ), (42901840801931/100000000000000 : ℝ), (1670974825863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344247643/10000000000 : ℝ)|^4223 ≤ (43730360577599/100000000000000 : ℝ)^3199
        have hw : |(5344247643/10000000000 : ℝ)|=(5344247643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267369321/10000000000 : ℝ)|^4223 ≤ (42901840801931/100000000000000 : ℝ)^3199
        have hw : |(5267369321/10000000000 : ℝ)|=(5267369321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272197633/1250000000 : ℝ)|^4223 ≤ (1670974825863/12500000000000 : ℝ)^3199
        have hw : |(-272197633/1250000000 : ℝ)|=(272197633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s7_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434926769/1000000000 : ℝ)*x 0 + (4225379843/10000000000 : ℝ)*x 1 + (34974017/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434926769/1000000000 : ℝ)^4223 ≤ (16658777880041/50000000000000 : ℝ)^3199 := by
    have hnat : (434926769 : ℕ)^4223*50000000000000^3199 ≤ 16658777880041^3199*1000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434926769 1000000000 16658777880041 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225379843/10000000000 : ℝ)^4223 ≤ (8017618393569/25000000000000 : ℝ)^3199 := by
    have hnat : (4225379843 : ℕ)^4223*25000000000000^3199 ≤ 8017618393569^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225379843 10000000000 8017618393569 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34974017/78125000 : ℝ)^4223 ≤ (6922394129669/20000000000000 : ℝ)^3199 := by
    have hnat : (34974017 : ℕ)^4223*20000000000000^3199 ≤ 6922394129669^3199*78125000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34974017 78125000 6922394129669 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434926769/1000000000 : ℝ), (4225379843/10000000000 : ℝ), (34974017/78125000 : ℝ)] ![(16658777880041/50000000000000 : ℝ), (8017618393569/25000000000000 : ℝ), (6922394129669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434926769/1000000000 : ℝ)|^4223 ≤ (16658777880041/50000000000000 : ℝ)^3199
        have hw : |(434926769/1000000000 : ℝ)|=(434926769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225379843/10000000000 : ℝ)|^4223 ≤ (8017618393569/25000000000000 : ℝ)^3199
        have hw : |(4225379843/10000000000 : ℝ)|=(4225379843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34974017/78125000 : ℝ)|^4223 ≤ (6922394129669/20000000000000 : ℝ)^3199
        have hw : |(34974017/78125000 : ℝ)|=(34974017/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s7_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-528728263/2500000000 : ℝ)*x 0 + (5267680663/10000000000 : ℝ)*x 1 + (1347667547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528728263/2500000000 : ℝ)^4223 ≤ (6431149945553/50000000000000 : ℝ)^3199 := by
    have hnat : (528728263 : ℕ)^4223*50000000000000^3199 ≤ 6431149945553^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528728263 2500000000 6431149945553 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267680663/10000000000 : ℝ)^4223 ≤ (13407871369/31250000000 : ℝ)^3199 := by
    have hnat : (5267680663 : ℕ)^4223*31250000000^3199 ≤ 13407871369^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267680663 10000000000 13407871369 31250000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347667547/2500000000 : ℝ)^4223 ≤ (44232511719117/100000000000000 : ℝ)^3199 := by
    have hnat : (1347667547 : ℕ)^4223*100000000000000^3199 ≤ 44232511719117^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347667547 2500000000 44232511719117 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528728263/2500000000 : ℝ), (5267680663/10000000000 : ℝ), (1347667547/2500000000 : ℝ)] ![(6431149945553/50000000000000 : ℝ), (13407871369/31250000000 : ℝ), (44232511719117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528728263/2500000000 : ℝ)|^4223 ≤ (6431149945553/50000000000000 : ℝ)^3199
        have hw : |(-528728263/2500000000 : ℝ)|=(528728263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267680663/10000000000 : ℝ)|^4223 ≤ (13407871369/31250000000 : ℝ)^3199
        have hw : |(5267680663/10000000000 : ℝ)|=(5267680663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347667547/2500000000 : ℝ)|^4223 ≤ (44232511719117/100000000000000 : ℝ)^3199
        have hw : |(1347667547/2500000000 : ℝ)|=(1347667547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s7_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656341861/5000000000 : ℝ)*x 0 + (-2054280047/10000000000 : ℝ)*x 1 + (5390670187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656341861/5000000000 : ℝ)^4223 ≤ (43389730496497/100000000000000 : ℝ)^3199 := by
    have hnat : (2656341861 : ℕ)^4223*100000000000000^3199 ≤ 43389730496497^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656341861 5000000000 43389730496497 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054280047/10000000000 : ℝ)^4223 ≤ (386804930611/3125000000000 : ℝ)^3199 := by
    have hnat : (2054280047 : ℕ)^4223*3125000000000^3199 ≤ 386804930611^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054280047 10000000000 386804930611 3125000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390670187/10000000000 : ℝ)^4223 ≤ (8846502341657/20000000000000 : ℝ)^3199 := by
    have hnat : (5390670187 : ℕ)^4223*20000000000000^3199 ≤ 8846502341657^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390670187 10000000000 8846502341657 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656341861/5000000000 : ℝ), (-2054280047/10000000000 : ℝ), (5390670187/10000000000 : ℝ)] ![(43389730496497/100000000000000 : ℝ), (386804930611/3125000000000 : ℝ), (8846502341657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656341861/5000000000 : ℝ)|^4223 ≤ (43389730496497/100000000000000 : ℝ)^3199
        have hw : |(2656341861/5000000000 : ℝ)|=(2656341861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2054280047/10000000000 : ℝ)|^4223 ≤ (386804930611/3125000000000 : ℝ)^3199
        have hw : |(-2054280047/10000000000 : ℝ)|=(2054280047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390670187/10000000000 : ℝ)|^4223 ≤ (8846502341657/20000000000000 : ℝ)^3199
        have hw : |(5390670187/10000000000 : ℝ)|=(5390670187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s7_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312683723/10000000000 : ℝ)*x 0 + (5390670187/10000000000 : ℝ)*x 1 + (-410856009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312683723/10000000000 : ℝ)^4223 ≤ (21694865253639/50000000000000 : ℝ)^3199 := by
    have hnat : (5312683723 : ℕ)^4223*50000000000000^3199 ≤ 21694865253639^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312683723 10000000000 21694865253639 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390670187/10000000000 : ℝ)^4223 ≤ (8846502341657/20000000000000 : ℝ)^3199 := by
    have hnat : (5390670187 : ℕ)^4223*20000000000000^3199 ≤ 8846502341657^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390670187 10000000000 8846502341657 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410856009/2000000000 : ℝ)^4223 ≤ (3094439440911/25000000000000 : ℝ)^3199 := by
    have hnat : (410856009 : ℕ)^4223*25000000000000^3199 ≤ 3094439440911^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410856009 2000000000 3094439440911 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312683723/10000000000 : ℝ), (5390670187/10000000000 : ℝ), (-410856009/2000000000 : ℝ)] ![(21694865253639/50000000000000 : ℝ), (8846502341657/20000000000000 : ℝ), (3094439440911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312683723/10000000000 : ℝ)|^4223 ≤ (21694865253639/50000000000000 : ℝ)^3199
        have hw : |(5312683723/10000000000 : ℝ)|=(5312683723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390670187/10000000000 : ℝ)|^4223 ≤ (8846502341657/20000000000000 : ℝ)^3199
        have hw : |(5390670187/10000000000 : ℝ)|=(5390670187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410856009/2000000000 : ℝ)|^4223 ≤ (3094439440911/25000000000000 : ℝ)^3199
        have hw : |(-410856009/2000000000 : ℝ)|=(410856009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s7_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349276577/10000000000 : ℝ)*x 0 + (895207981/2000000000 : ℝ)*x 1 + (4226016953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349276577/10000000000 : ℝ)^4223 ≤ (8329411407749/25000000000000 : ℝ)^3199 := by
    have hnat : (4349276577 : ℕ)^4223*25000000000000^3199 ≤ 8329411407749^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349276577 10000000000 8329411407749 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895207981/2000000000 : ℝ)^4223 ≤ (17302748547821/50000000000000 : ℝ)^3199 := by
    have hnat : (895207981 : ℕ)^4223*50000000000000^3199 ≤ 17302748547821^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895207981 2000000000 17302748547821 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226016953/10000000000 : ℝ)^4223 ≤ (32076857257973/100000000000000 : ℝ)^3199 := by
    have hnat : (4226016953 : ℕ)^4223*100000000000000^3199 ≤ 32076857257973^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226016953 10000000000 32076857257973 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349276577/10000000000 : ℝ), (895207981/2000000000 : ℝ), (4226016953/10000000000 : ℝ)] ![(8329411407749/25000000000000 : ℝ), (17302748547821/50000000000000 : ℝ), (32076857257973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349276577/10000000000 : ℝ)|^4223 ≤ (8329411407749/25000000000000 : ℝ)^3199
        have hw : |(4349276577/10000000000 : ℝ)|=(4349276577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895207981/2000000000 : ℝ)|^4223 ≤ (17302748547821/50000000000000 : ℝ)^3199
        have hw : |(895207981/2000000000 : ℝ)|=(895207981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226016953/10000000000 : ℝ)|^4223 ≤ (32076857257973/100000000000000 : ℝ)^3199
        have hw : |(4226016953/10000000000 : ℝ)|=(4226016953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2873/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (359/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (359/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (359/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (359/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (359/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (359/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (359/3125 : ℝ) ^ (8445/2048 : ℝ) ≤ (6665839620574173/50000000000000000000 : ℝ) := by
    have hpowers : (359/3125 : ℝ)^8445 ≤ (6665839620574173/50000000000000000000 : ℝ)^2048 := by
      have hnat : (359 : ℕ)^8445*50000000000000000000^2048 ≤ 6665839620574173^2048*3125^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        359 3125 6665839620574173 50000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (359/3125 : ℝ)) (X := (6665839620574173/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (8445/2048 : ℝ) ≤ (31156764110787487/100000000000000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^8445 ≤ (31156764110787487/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7057 : ℕ)^8445*100000000000000000000^2048 ≤ 31156764110787487^2048*50000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 31156764110787487 100000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (31156764110787487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006665839620574173/25000000000000000000 : ℝ) ≤ (5000323274390351/5000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (25006665839620574173/25000000000000000000 : ℝ)^2048 ≤ (5000323274390351/5000000000000000 : ℝ)^8445 := by
      have hnat : (25006665839620574173 : ℕ)^2048*5000000000000000^8445 ≤ 5000323274390351^8445*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006665839620574173 25000000000000000000 5000323274390351 5000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000323274390351/5000000000000000 : ℝ)) (X := (25006665839620574173/25000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044488443351935833/100000000000000000000 : ℝ) ≤ (10001078709103241/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (100044488443351935833/100000000000000000000 : ℝ)^2048 ≤ (10001078709103241/10000000000000000 : ℝ)^8445 := by
      have hnat : (100044488443351935833 : ℕ)^2048*10000000000000000^8445 ≤ 10001078709103241^8445*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044488443351935833 100000000000000000000 10001078709103241 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001078709103241/10000000000000000 : ℝ)) (X := (100044488443351935833/100000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031156764110787487/50000000000000000000 : ℝ) ≤ (500075543471289/500000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (50031156764110787487/50000000000000000000 : ℝ)^2048 ≤ (500075543471289/500000000000000 : ℝ)^8445 := by
      have hnat : (50031156764110787487 : ℕ)^2048*500000000000000^8445 ≤ 500075543471289^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031156764110787487 50000000000000000000 500075543471289 500000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500075543471289/500000000000000 : ℝ)) (X := (50031156764110787487/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6665839620574173/50000000000000000000 : ℝ) ≤ ((6562942130381866847/6565000000000000000 : ℝ)+2*(432160322539/262600000000000 : ℝ)*(359/3125 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (6562942130381866847/6565000000000000000 : ℝ)+2*(432160322539/262600000000000 : ℝ)*(359/3125 : ℝ)=(5000323274390351/5000000000000000 : ℝ) by norm_num, show 1+2*(6665839620574173/50000000000000000000 : ℝ)=(25006665839620574173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31156764110787487/100000000000000000000 : ℝ)+(6665839620574173/50000000000000000000 : ℝ) ≤ ((6562942130381866847/6565000000000000000 : ℝ)+(432160322539/262600000000000 : ℝ)*((7057/50000 : ℝ)+(359/3125 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (6562942130381866847/6565000000000000000 : ℝ)+(432160322539/262600000000000 : ℝ)*((7057/50000 : ℝ)+(359/3125 : ℝ))=(10001078709103241/10000000000000000 : ℝ) by norm_num, show 1+(31156764110787487/100000000000000000000 : ℝ)+(6665839620574173/50000000000000000000 : ℝ)=(100044488443351935833/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31156764110787487/100000000000000000000 : ℝ) ≤ ((6562942130381866847/6565000000000000000 : ℝ)+2*(432160322539/262600000000000 : ℝ)*(7057/50000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (6562942130381866847/6565000000000000000 : ℝ)+2*(432160322539/262600000000000 : ℝ)*(7057/50000 : ℝ)=(500075543471289/500000000000000 : ℝ) by norm_num, show 1+2*(31156764110787487/100000000000000000000 : ℝ)=(50031156764110787487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6562942130381866847/6565000000000000000 : ℝ)*(X 1 0+X 2 0)+(432160322539/262600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (359/3125 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6562942130381866847/6565000000000000000 : ℝ)) (alpha := (432160322539/262600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6562942130381866847/6565000000000000000 : ℝ)*(X 0 1+X 2 1)+(432160322539/262600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (359/3125 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6562942130381866847/6565000000000000000 : ℝ)) (alpha := (432160322539/262600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6562942130381866847/6565000000000000000 : ℝ)*(X 0 2+X 1 2)+(432160322539/262600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (359/3125 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6562942130381866847/6565000000000000000 : ℝ)) (alpha := (432160322539/262600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211490783/1000000000 : ℝ)*X 0 0+(5390983509/10000000000 : ℝ)*X 0 1+(5267368911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344247809/10000000000 : ℝ)*X 1 0+(-1088790469/5000000000 : ℝ)*X 1 1+(5267369249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344247643/10000000000 : ℝ)*X 2 0+(5267369321/10000000000 : ℝ)*X 2 1+(-272197633/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434926769/1000000000 : ℝ)*X 0 0+(4225379843/10000000000 : ℝ)*X 0 1+(34974017/78125000 : ℝ)*X 0 2+(434926769/1000000000 : ℝ)*X 1 0+(4225379843/10000000000 : ℝ)*X 1 1+(34974017/78125000 : ℝ)*X 1 2+(434926769/1000000000 : ℝ)*X 2 0+(4225379843/10000000000 : ℝ)*X 2 1+(34974017/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528728263/2500000000 : ℝ)*X 0 0+(5267680663/10000000000 : ℝ)*X 0 1+(1347667547/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656341861/5000000000 : ℝ)*X 1 0+(-2054280047/10000000000 : ℝ)*X 1 1+(5390670187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312683723/10000000000 : ℝ)*X 2 0+(5390670187/10000000000 : ℝ)*X 2 1+(-410856009/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349276577/10000000000 : ℝ)*X 0 0+(895207981/2000000000 : ℝ)*X 0 1+(4226016953/10000000000 : ℝ)*X 0 2+(4349276577/10000000000 : ℝ)*X 1 0+(895207981/2000000000 : ℝ)*X 1 1+(4226016953/10000000000 : ℝ)*X 1 2+(4349276577/10000000000 : ℝ)*X 2 0+(895207981/2000000000 : ℝ)*X 2 1+(4226016953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87640843247639132708057319/25250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46649981/100000000000000 : ℝ)*(base8) + (58341607/100000000000000 : ℝ)*(base15) + (128330633/50000000000000 : ℝ)*(lower2) + (104528231/25000000000000 : ℝ)*(lower4) + (49943173/100000000000000 : ℝ)*(lower5) + (6034574569207033/100000000000000 : ℝ)*(major0) + (6034574569207033/100000000000000 : ℝ)*(major1) + (6034574569207033/100000000000000 : ℝ)*(major2) + (4044846123996817/50000000000000 : ℝ)*(sp0) + (808971391279473/10000000000000 : ℝ)*(sp1) + (8089713971136337/100000000000000 : ℝ)*(sp2) + (3979417437809189/100000000000000 : ℝ)*(sp3) + (21676492721/100000000000000 : ℝ)*(sp4) + (8806885523/50000000000000 : ℝ)*(sp7) + (795887010316047/20000000000000 : ℝ)*(f.failure) + (8089713971136337/100000000000000 : ℝ)*(f.sum) + (124756264654413/13130000000000000000000000000 : ℝ)*base66 + (6976030626457390049/656500000000000000000000000000000 : ℝ)*base68 + (8459101243654390049/656500000000000000000000000000000 : ℝ)*base70 + (3799408597208609951/656500000000000000000000000000000 : ℝ)*base71 + (82829115062423/13130000000000000000000000000 : ℝ)*base74 + (13139720101433609951/656500000000000000000000000000000 : ℝ)*base75 + (6310746197272109951/656500000000000000000000000000000 : ℝ)*base77 + (3712326752930609951/656500000000000000000000000000000 : ℝ)*base79 + (13231085784633/13130000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4049953/1000000000000000000000 : ℝ)*base90 + (4049953/1000000000000000000000 : ℝ)*base92 + (4049953/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (924357508959210554479724067/328250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126857913/25000000000000 : ℝ)*(base19) + (68952777/12500000000000 : ℝ)*(base23) + (56663261/100000000000000 : ℝ)*(upper3) + (9503959/50000000000000 : ℝ)*(lower4) + (11407989/20000000000000 : ℝ)*(upper5) + (6065203005902913/100000000000000 : ℝ)*(major0) + (6065203005902913/100000000000000 : ℝ)*(major1) + (6065203005902913/100000000000000 : ℝ)*(major2) + (286154591/2000000000000 : ℝ)*(sp1) + (773305323/5000000000000 : ℝ)*(sp2) + (8130773274437851/100000000000000 : ℝ)*(sp4) + (8130758459276649/100000000000000 : ℝ)*(sp5) + (325230290268367/4000000000000 : ℝ)*(sp6) + (1999816321750369/50000000000000 : ℝ)*(sp7) + (1999816321750369/50000000000000 : ℝ)*(f.failure) + (8130773274437851/100000000000000 : ℝ)*(f.sum) + (82757448540513/13130000000000000000000000000 : ℝ)*base66 + (1456476480941399689/656500000000000000000000000000000 : ℝ)*base68 + (3658727170415100311/656500000000000000000000000000000 : ℝ)*base69 + (102216933722899689/656500000000000000000000000000000 : ℝ)*base72 + (3045571908203/13130000000000000000000000000 : ℝ)*base74 + (14042137754552600311/656500000000000000000000000000000 : ℝ)*base75 + (6843376614176600311/656500000000000000000000000000000 : ℝ)*base77 + (6278535080140600311/656500000000000000000000000000000 : ℝ)*base79 + (43840141419237/13130000000000000000000000000 : ℝ)*base81 + (24931631/2500000000000000000000 : ℝ)*base90 + (24931631/2500000000000000000000 : ℝ)*base92 + (24931631/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1253_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2873/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1253_box_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991552479/10000000000 : ℝ)*x 0 + (5374676979/10000000000 : ℝ)*x 1 + (2687339061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991552479/10000000000 : ℝ)^4223 ≤ (2376254812373/20000000000000 : ℝ)^3199 := by
    have hnat : (1991552479 : ℕ)^4223*20000000000000^3199 ≤ 2376254812373^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991552479 10000000000 2376254812373 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374676979/10000000000 : ℝ)^4223 ≤ (44059356779701/100000000000000 : ℝ)^3199 := by
    have hnat : (5374676979 : ℕ)^4223*100000000000000^3199 ≤ 44059356779701^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374676979 10000000000 44059356779701 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687339061/5000000000 : ℝ)^4223 ≤ (44059369148823/100000000000000 : ℝ)^3199 := by
    have hnat : (2687339061 : ℕ)^4223*100000000000000^3199 ≤ 44059369148823^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687339061 5000000000 44059369148823 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991552479/10000000000 : ℝ), (5374676979/10000000000 : ℝ), (2687339061/5000000000 : ℝ)] ![(2376254812373/20000000000000 : ℝ), (44059356779701/100000000000000 : ℝ), (44059369148823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991552479/10000000000 : ℝ)|^4223 ≤ (2376254812373/20000000000000 : ℝ)^3199
        have hw : |(-1991552479/10000000000 : ℝ)|=(1991552479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374676979/10000000000 : ℝ)|^4223 ≤ (44059356779701/100000000000000 : ℝ)^3199
        have hw : |(5374676979/10000000000 : ℝ)|=(5374676979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687339061/5000000000 : ℝ)|^4223 ≤ (44059369148823/100000000000000 : ℝ)^3199
        have hw : |(2687339061/5000000000 : ℝ)|=(2687339061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52968699/100000000 : ℝ)*x 0 + (-1048665093/5000000000 : ℝ)*x 1 + (2687338669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52968699/100000000 : ℝ)^4223 ≤ (10804828700597/25000000000000 : ℝ)^3199 := by
    have hnat : (52968699 : ℕ)^4223*25000000000000^3199 ≤ 10804828700597^3199*100000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52968699 100000000 10804828700597 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048665093/5000000000 : ℝ)^4223 ≤ (63606622573/500000000000 : ℝ)^3199 := by
    have hnat : (1048665093 : ℕ)^4223*500000000000^3199 ≤ 63606622573^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048665093 5000000000 63606622573 500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687338669/5000000000 : ℝ)^4223 ≤ (22029680332333/50000000000000 : ℝ)^3199 := by
    have hnat : (2687338669 : ℕ)^4223*50000000000000^3199 ≤ 22029680332333^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687338669 5000000000 22029680332333 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52968699/100000000 : ℝ), (-1048665093/5000000000 : ℝ), (2687338669/5000000000 : ℝ)] ![(10804828700597/25000000000000 : ℝ), (63606622573/500000000000 : ℝ), (22029680332333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52968699/100000000 : ℝ)|^4223 ≤ (10804828700597/25000000000000 : ℝ)^3199
        have hw : |(52968699/100000000 : ℝ)|=(52968699/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048665093/5000000000 : ℝ)|^4223 ≤ (63606622573/500000000000 : ℝ)^3199
        have hw : |(-1048665093/5000000000 : ℝ)|=(1048665093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687338669/5000000000 : ℝ)|^4223 ≤ (22029680332333/50000000000000 : ℝ)^3199
        have hw : |(2687338669/5000000000 : ℝ)|=(2687338669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296869677/10000000000 : ℝ)*x 0 + (2687338519/5000000000 : ℝ)*x 1 + (-2097330891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296869677/10000000000 : ℝ)^4223 ≤ (10804828100101/25000000000000 : ℝ)^3199 := by
    have hnat : (5296869677 : ℕ)^4223*25000000000000^3199 ≤ 10804828100101^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296869677 10000000000 10804828100101 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687338519/5000000000 : ℝ)^4223 ≤ (22029678709089/50000000000000 : ℝ)^3199 := by
    have hnat : (2687338519 : ℕ)^4223*50000000000000^3199 ≤ 22029678709089^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687338519 5000000000 22029678709089 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097330891/10000000000 : ℝ)^4223 ≤ (795083134973/6250000000000 : ℝ)^3199 := by
    have hnat : (2097330891 : ℕ)^4223*6250000000000^3199 ≤ 795083134973^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097330891 10000000000 795083134973 6250000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296869677/10000000000 : ℝ), (2687338519/5000000000 : ℝ), (-2097330891/10000000000 : ℝ)] ![(10804828100101/25000000000000 : ℝ), (22029678709089/50000000000000 : ℝ), (795083134973/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296869677/10000000000 : ℝ)|^4223 ≤ (10804828100101/25000000000000 : ℝ)^3199
        have hw : |(5296869677/10000000000 : ℝ)|=(5296869677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687338519/5000000000 : ℝ)|^4223 ≤ (22029678709089/50000000000000 : ℝ)^3199
        have hw : |(2687338519/5000000000 : ℝ)|=(2687338519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097330891/10000000000 : ℝ)|^4223 ≤ (795083134973/6250000000000 : ℝ)^3199
        have hw : |(-2097330891/10000000000 : ℝ)|=(2097330891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (278480907/625000000 : ℝ)*x 0 + (4298091519/10000000000 : ℝ)*x 1 + (67157653/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278480907/625000000 : ℝ)^4223 ≤ (8599500518629/25000000000000 : ℝ)^3199 := by
    have hnat : (278480907 : ℕ)^4223*25000000000000^3199 ≤ 8599500518629^3199*625000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278480907 625000000 8599500518629 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4298091519/10000000000 : ℝ)^4223 ≤ (16400503826873/50000000000000 : ℝ)^3199 := by
    have hnat : (4298091519 : ℕ)^4223*50000000000000^3199 ≤ 16400503826873^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298091519 10000000000 16400503826873 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67157653/156250000 : ℝ)^4223 ≤ (32800990255291/100000000000000 : ℝ)^3199 := by
    have hnat : (67157653 : ℕ)^4223*100000000000000^3199 ≤ 32800990255291^3199*156250000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67157653 156250000 32800990255291 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(278480907/625000000 : ℝ), (4298091519/10000000000 : ℝ), (67157653/156250000 : ℝ)] ![(8599500518629/25000000000000 : ℝ), (16400503826873/50000000000000 : ℝ), (32800990255291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(278480907/625000000 : ℝ)|^4223 ≤ (8599500518629/25000000000000 : ℝ)^3199
        have hw : |(278480907/625000000 : ℝ)|=(278480907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4298091519/10000000000 : ℝ)|^4223 ≤ (16400503826873/50000000000000 : ℝ)^3199
        have hw : |(4298091519/10000000000 : ℝ)|=(4298091519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67157653/156250000 : ℝ)|^4223 ≤ (32800990255291/100000000000000 : ℝ)^3199
        have hw : |(67157653/156250000 : ℝ)|=(67157653/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2239649273/10000000000 : ℝ)*x 0 + (1320598607/2500000000 : ℝ)*x 1 + (5282394433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239649273/10000000000 : ℝ)^4223 ≤ (13873071212161/100000000000000 : ℝ)^3199 := by
    have hnat : (2239649273 : ℕ)^4223*100000000000000^3199 ≤ 13873071212161^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239649273 10000000000 13873071212161 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320598607/2500000000 : ℝ)^4223 ≤ (43063464363143/100000000000000 : ℝ)^3199 := by
    have hnat : (1320598607 : ℕ)^4223*100000000000000^3199 ≤ 43063464363143^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320598607 2500000000 43063464363143 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282394433/10000000000 : ℝ)^4223 ≤ (5382933052119/12500000000000 : ℝ)^3199 := by
    have hnat : (5282394433 : ℕ)^4223*12500000000000^3199 ≤ 5382933052119^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282394433 10000000000 5382933052119 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2239649273/10000000000 : ℝ), (1320598607/2500000000 : ℝ), (5282394433/10000000000 : ℝ)] ![(13873071212161/100000000000000 : ℝ), (43063464363143/100000000000000 : ℝ), (5382933052119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2239649273/10000000000 : ℝ)|^4223 ≤ (13873071212161/100000000000000 : ℝ)^3199
        have hw : |(-2239649273/10000000000 : ℝ)|=(2239649273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320598607/2500000000 : ℝ)|^4223 ≤ (43063464363143/100000000000000 : ℝ)^3199
        have hw : |(1320598607/2500000000 : ℝ)|=(1320598607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282394433/10000000000 : ℝ)|^4223 ≤ (5382933052119/12500000000000 : ℝ)^3199
        have hw : |(5282394433/10000000000 : ℝ)|=(5282394433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167559583/312500000 : ℝ)*x 0 + (-333429/1562500 : ℝ)*x 1 + (132059861/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167559583/312500000 : ℝ)^4223 ≤ (43921213668333/100000000000000 : ℝ)^3199 := by
    have hnat : (167559583 : ℕ)^4223*100000000000000^3199 ≤ 43921213668333^3199*312500000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167559583 312500000 43921213668333 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333429/1562500 : ℝ)^4223 ≤ (13015321827831/100000000000000 : ℝ)^3199 := by
    have hnat : (333429 : ℕ)^4223*100000000000000^3199 ≤ 13015321827831^3199*1562500^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333429 1562500 13015321827831 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132059861/250000000 : ℝ)^4223 ≤ (8612692898457/20000000000000 : ℝ)^3199 := by
    have hnat : (132059861 : ℕ)^4223*20000000000000^3199 ≤ 8612692898457^3199*250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132059861 250000000 8612692898457 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167559583/312500000 : ℝ), (-333429/1562500 : ℝ), (132059861/250000000 : ℝ)] ![(43921213668333/100000000000000 : ℝ), (13015321827831/100000000000000 : ℝ), (8612692898457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167559583/312500000 : ℝ)|^4223 ≤ (43921213668333/100000000000000 : ℝ)^3199
        have hw : |(167559583/312500000 : ℝ)|=(167559583/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-333429/1562500 : ℝ)|^4223 ≤ (13015321827831/100000000000000 : ℝ)^3199
        have hw : |(-333429/1562500 : ℝ)|=(333429/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132059861/250000000 : ℝ)|^4223 ≤ (8612692898457/20000000000000 : ℝ)^3199
        have hw : |(132059861/250000000 : ℝ)|=(132059861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268095333/500000000 : ℝ)*x 0 + (2641197213/5000000000 : ℝ)*x 1 + (-2133945613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268095333/500000000 : ℝ)^4223 ≤ (43921213711587/100000000000000 : ℝ)^3199 := by
    have hnat : (268095333 : ℕ)^4223*100000000000000^3199 ≤ 43921213711587^3199*500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268095333 500000000 43921213711587 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641197213/5000000000 : ℝ)^4223 ≤ (2153173217081/5000000000000 : ℝ)^3199 := by
    have hnat : (2641197213 : ℕ)^4223*5000000000000^3199 ≤ 2153173217081^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641197213 5000000000 2153173217081 5000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133945613/10000000000 : ℝ)^4223 ≤ (5206128773/40000000000 : ℝ)^3199 := by
    have hnat : (2133945613 : ℕ)^4223*40000000000^3199 ≤ 5206128773^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133945613 10000000000 5206128773 40000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268095333/500000000 : ℝ), (2641197213/5000000000 : ℝ), (-2133945613/10000000000 : ℝ)] ![(43921213711587/100000000000000 : ℝ), (2153173217081/5000000000000 : ℝ), (5206128773/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268095333/500000000 : ℝ)|^4223 ≤ (43921213711587/100000000000000 : ℝ)^3199
        have hw : |(268095333/500000000 : ℝ)|=(268095333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641197213/5000000000 : ℝ)|^4223 ≤ (2153173217081/5000000000000 : ℝ)^3199
        have hw : |(2641197213/5000000000 : ℝ)|=(2641197213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2133945613/10000000000 : ℝ)|^4223 ≤ (5206128773/40000000000 : ℝ)^3199
        have hw : |(-2133945613/10000000000 : ℝ)|=(2133945613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121218447/5000000000 : ℝ)*x 0 + (880939887/2000000000 : ℝ)*x 1 + (68823429/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121218447/5000000000 : ℝ)^4223 ≤ (16120743587921/50000000000000 : ℝ)^3199 := by
    have hnat : (2121218447 : ℕ)^4223*50000000000000^3199 ≤ 16120743587921^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121218447 5000000000 16120743587921 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880939887/2000000000 : ℝ)^4223 ≤ (16939628148779/50000000000000 : ℝ)^3199 := by
    have hnat : (880939887 : ℕ)^4223*50000000000000^3199 ≤ 16939628148779^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880939887 2000000000 16939628148779 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68823429/156250000 : ℝ)^4223 ≤ (6775851302157/20000000000000 : ℝ)^3199 := by
    have hnat : (68823429 : ℕ)^4223*20000000000000^3199 ≤ 6775851302157^3199*156250000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68823429 156250000 6775851302157 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121218447/5000000000 : ℝ), (880939887/2000000000 : ℝ), (68823429/156250000 : ℝ)] ![(16120743587921/50000000000000 : ℝ), (16939628148779/50000000000000 : ℝ), (6775851302157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121218447/5000000000 : ℝ)|^4223 ≤ (16120743587921/50000000000000 : ℝ)^3199
        have hw : |(2121218447/5000000000 : ℝ)|=(2121218447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880939887/2000000000 : ℝ)|^4223 ≤ (16939628148779/50000000000000 : ℝ)^3199
        have hw : |(880939887/2000000000 : ℝ)|=(880939887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68823429/156250000 : ℝ)|^4223 ≤ (6775851302157/20000000000000 : ℝ)^3199
        have hw : |(68823429/156250000 : ℝ)|=(68823429/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_8 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2187649659/10000000000 : ℝ)*x 0 + (1043885413/2000000000 : ℝ)*x 1 + (5384291197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187649659/10000000000 : ℝ)^4223 ≤ (537978139989/4000000000000 : ℝ)^3199 := by
    have hnat : (2187649659 : ℕ)^4223*4000000000000^3199 ≤ 537978139989^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187649659 10000000000 537978139989 4000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043885413/2000000000 : ℝ)^4223 ≤ (42387118435721/100000000000000 : ℝ)^3199 := by
    have hnat : (1043885413 : ℕ)^4223*100000000000000^3199 ≤ 42387118435721^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043885413 2000000000 42387118435721 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384291197/10000000000 : ℝ)^4223 ≤ (2760214253199/6250000000000 : ℝ)^3199 := by
    have hnat : (5384291197 : ℕ)^4223*6250000000000^3199 ≤ 2760214253199^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384291197 10000000000 2760214253199 6250000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2187649659/10000000000 : ℝ), (1043885413/2000000000 : ℝ), (5384291197/10000000000 : ℝ)] ![(537978139989/4000000000000 : ℝ), (42387118435721/100000000000000 : ℝ), (2760214253199/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2187649659/10000000000 : ℝ)|^4223 ≤ (537978139989/4000000000000 : ℝ)^3199
        have hw : |(-2187649659/10000000000 : ℝ)|=(2187649659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043885413/2000000000 : ℝ)|^4223 ≤ (42387118435721/100000000000000 : ℝ)^3199
        have hw : |(1043885413/2000000000 : ℝ)|=(1043885413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384291197/10000000000 : ℝ)|^4223 ≤ (2760214253199/6250000000000 : ℝ)^3199
        have hw : |(5384291197/10000000000 : ℝ)|=(5384291197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_9 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290091183/10000000000 : ℝ)*x 0 + (-261681179/1250000000 : ℝ)*x 1 + (5384290917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290091183/10000000000 : ℝ)^4223 ≤ (10786578655793/25000000000000 : ℝ)^3199 := by
    have hnat : (5290091183 : ℕ)^4223*25000000000000^3199 ≤ 10786578655793^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290091183 10000000000 10786578655793 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261681179/1250000000 : ℝ)^4223 ≤ (12690260341923/100000000000000 : ℝ)^3199 := by
    have hnat : (261681179 : ℕ)^4223*100000000000000^3199 ≤ 12690260341923^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261681179 1250000000 12690260341923 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384290917/10000000000 : ℝ)^4223 ≤ (22081712509697/50000000000000 : ℝ)^3199 := by
    have hnat : (5384290917 : ℕ)^4223*50000000000000^3199 ≤ 22081712509697^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384290917 10000000000 22081712509697 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290091183/10000000000 : ℝ), (-261681179/1250000000 : ℝ), (5384290917/10000000000 : ℝ)] ![(10786578655793/25000000000000 : ℝ), (12690260341923/100000000000000 : ℝ), (22081712509697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290091183/10000000000 : ℝ)|^4223 ≤ (10786578655793/25000000000000 : ℝ)^3199
        have hw : |(5290091183/10000000000 : ℝ)|=(5290091183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261681179/1250000000 : ℝ)|^4223 ≤ (12690260341923/100000000000000 : ℝ)^3199
        have hw : |(-261681179/1250000000 : ℝ)|=(261681179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384290917/10000000000 : ℝ)|^4223 ≤ (22081712509697/50000000000000 : ℝ)^3199
        have hw : |(5384290917/10000000000 : ℝ)|=(5384290917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_10 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645045479/5000000000 : ℝ)*x 0 + (5384291419/10000000000 : ℝ)*x 1 + (-65420283/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645045479/5000000000 : ℝ)^4223 ≤ (21573156100319/50000000000000 : ℝ)^3199 := by
    have hnat : (2645045479 : ℕ)^4223*50000000000000^3199 ≤ 21573156100319^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645045479 5000000000 21573156100319 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384291419/10000000000 : ℝ)^4223 ≤ (552042880687/1250000000000 : ℝ)^3199 := by
    have hnat : (5384291419 : ℕ)^4223*1250000000000^3199 ≤ 552042880687^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384291419 10000000000 552042880687 1250000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65420283/312500000 : ℝ)^4223 ≤ (6345128666529/50000000000000 : ℝ)^3199 := by
    have hnat : (65420283 : ℕ)^4223*50000000000000^3199 ≤ 6345128666529^3199*312500000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65420283 312500000 6345128666529 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645045479/5000000000 : ℝ), (5384291419/10000000000 : ℝ), (-65420283/312500000 : ℝ)] ![(21573156100319/50000000000000 : ℝ), (552042880687/1250000000000 : ℝ), (6345128666529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645045479/5000000000 : ℝ)|^4223 ≤ (21573156100319/50000000000000 : ℝ)^3199
        have hw : |(2645045479/5000000000 : ℝ)|=(2645045479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384291419/10000000000 : ℝ)|^4223 ≤ (552042880687/1250000000000 : ℝ)^3199
        have hw : |(5384291419/10000000000 : ℝ)|=(5384291419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65420283/312500000 : ℝ)|^4223 ≤ (6345128666529/50000000000000 : ℝ)^3199
        have hw : |(-65420283/312500000 : ℝ)|=(65420283/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_11 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2238818527/5000000000 : ℝ)*x 0 + (2143489411/5000000000 : ℝ)*x 1 + (857395773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238818527/5000000000 : ℝ)^4223 ≤ (17310899309999/50000000000000 : ℝ)^3199 := by
    have hnat : (2238818527 : ℕ)^4223*50000000000000^3199 ≤ 17310899309999^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238818527 5000000000 17310899309999 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143489411/5000000000 : ℝ)^4223 ≤ (32689100465539/100000000000000 : ℝ)^3199 := by
    have hnat : (2143489411 : ℕ)^4223*100000000000000^3199 ≤ 32689100465539^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143489411 5000000000 32689100465539 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857395773/2000000000 : ℝ)^4223 ≤ (16344550449189/50000000000000 : ℝ)^3199 := by
    have hnat : (857395773 : ℕ)^4223*50000000000000^3199 ≤ 16344550449189^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857395773 2000000000 16344550449189 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238818527/5000000000 : ℝ), (2143489411/5000000000 : ℝ), (857395773/2000000000 : ℝ)] ![(17310899309999/50000000000000 : ℝ), (32689100465539/100000000000000 : ℝ), (16344550449189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238818527/5000000000 : ℝ)|^4223 ≤ (17310899309999/50000000000000 : ℝ)^3199
        have hw : |(2238818527/5000000000 : ℝ)|=(2238818527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2143489411/5000000000 : ℝ)|^4223 ≤ (32689100465539/100000000000000 : ℝ)^3199
        have hw : |(2143489411/5000000000 : ℝ)|=(2143489411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(857395773/2000000000 : ℝ)|^4223 ≤ (16344550449189/50000000000000 : ℝ)^3199
        have hw : |(857395773/2000000000 : ℝ)|=(857395773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_12 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043805487/10000000000 : ℝ)*x 0 + (5436443461/10000000000 : ℝ)*x 1 + (5274310917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043805487/10000000000 : ℝ)^4223 ≤ (12294510511861/100000000000000 : ℝ)^3199 := by
    have hnat : (2043805487 : ℕ)^4223*100000000000000^3199 ≤ 12294510511861^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043805487 10000000000 12294510511861 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436443461/10000000000 : ℝ)^4223 ≤ (44728996946957/100000000000000 : ℝ)^3199 := by
    have hnat : (5436443461 : ℕ)^4223*100000000000000^3199 ≤ 44728996946957^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436443461 10000000000 44728996946957 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274310917/10000000000 : ℝ)^4223 ≤ (8595298507111/20000000000000 : ℝ)^3199 := by
    have hnat : (5274310917 : ℕ)^4223*20000000000000^3199 ≤ 8595298507111^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274310917 10000000000 8595298507111 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043805487/10000000000 : ℝ), (5436443461/10000000000 : ℝ), (5274310917/10000000000 : ℝ)] ![(12294510511861/100000000000000 : ℝ), (44728996946957/100000000000000 : ℝ), (8595298507111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043805487/10000000000 : ℝ)|^4223 ≤ (12294510511861/100000000000000 : ℝ)^3199
        have hw : |(-2043805487/10000000000 : ℝ)|=(2043805487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436443461/10000000000 : ℝ)|^4223 ≤ (44728996946957/100000000000000 : ℝ)^3199
        have hw : |(5436443461/10000000000 : ℝ)|=(5436443461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274310917/10000000000 : ℝ)|^4223 ≤ (8595298507111/20000000000000 : ℝ)^3199
        have hw : |(5274310917/10000000000 : ℝ)|=(5274310917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_13 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341900543/2500000000 : ℝ)*x 0 + (-2137096841/10000000000 : ℝ)*x 1 + (1318577621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341900543/2500000000 : ℝ)^4223 ≤ (21991405990103/50000000000000 : ℝ)^3199 := by
    have hnat : (1341900543 : ℕ)^4223*50000000000000^3199 ≤ 21991405990103^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341900543 2500000000 21991405990103 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2137096841/10000000000 : ℝ)^4223 ≤ (6520350066803/50000000000000 : ℝ)^3199 := by
    have hnat : (2137096841 : ℕ)^4223*50000000000000^3199 ≤ 6520350066803^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137096841 10000000000 6520350066803 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318577621/2500000000 : ℝ)^4223 ≤ (42976487877979/100000000000000 : ℝ)^3199 := by
    have hnat : (1318577621 : ℕ)^4223*100000000000000^3199 ≤ 42976487877979^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318577621 2500000000 42976487877979 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341900543/2500000000 : ℝ), (-2137096841/10000000000 : ℝ), (1318577621/2500000000 : ℝ)] ![(21991405990103/50000000000000 : ℝ), (6520350066803/50000000000000 : ℝ), (42976487877979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341900543/2500000000 : ℝ)|^4223 ≤ (21991405990103/50000000000000 : ℝ)^3199
        have hw : |(1341900543/2500000000 : ℝ)|=(1341900543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2137096841/10000000000 : ℝ)|^4223 ≤ (6520350066803/50000000000000 : ℝ)^3199
        have hw : |(-2137096841/10000000000 : ℝ)|=(2137096841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318577621/2500000000 : ℝ)|^4223 ≤ (42976487877979/100000000000000 : ℝ)^3199
        have hw : |(1318577621/2500000000 : ℝ)|=(1318577621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_14 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683800979/5000000000 : ℝ)*x 0 + (5274310559/10000000000 : ℝ)*x 1 + (-2137097027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683800979/5000000000 : ℝ)^4223 ≤ (43982809665353/100000000000000 : ℝ)^3199 := by
    have hnat : (2683800979 : ℕ)^4223*100000000000000^3199 ≤ 43982809665353^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683800979 5000000000 43982809665353 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274310559/10000000000 : ℝ)^4223 ≤ (21488244342359/50000000000000 : ℝ)^3199 := by
    have hnat : (5274310559 : ℕ)^4223*50000000000000^3199 ≤ 21488244342359^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274310559 10000000000 21488244342359 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2137097027/10000000000 : ℝ)^4223 ≤ (6520350815949/50000000000000 : ℝ)^3199 := by
    have hnat : (2137097027 : ℕ)^4223*50000000000000^3199 ≤ 6520350815949^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137097027 10000000000 6520350815949 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683800979/5000000000 : ℝ), (5274310559/10000000000 : ℝ), (-2137097027/10000000000 : ℝ)] ![(43982809665353/100000000000000 : ℝ), (21488244342359/50000000000000 : ℝ), (6520350815949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683800979/5000000000 : ℝ)|^4223 ≤ (43982809665353/100000000000000 : ℝ)^3199
        have hw : |(2683800979/5000000000 : ℝ)|=(2683800979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274310559/10000000000 : ℝ)|^4223 ≤ (21488244342359/50000000000000 : ℝ)^3199
        have hw : |(5274310559/10000000000 : ℝ)|=(5274310559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2137097027/10000000000 : ℝ)|^4223 ≤ (6520350815949/50000000000000 : ℝ)^3199
        have hw : |(-2137097027/10000000000 : ℝ)|=(2137097027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_box_15 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168940981/400000000 : ℝ)*x 0 + (882806539/2000000000 : ℝ)*x 1 + (176561321/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168940981/400000000 : ℝ)^4223 ≤ (32051885504607/100000000000000 : ℝ)^3199 := by
    have hnat : (168940981 : ℕ)^4223*100000000000000^3199 ≤ 32051885504607^3199*400000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168940981 400000000 32051885504607 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882806539/2000000000 : ℝ)^4223 ≤ (4246756945703/12500000000000 : ℝ)^3199 := by
    have hnat : (882806539 : ℕ)^4223*12500000000000^3199 ≤ 4246756945703^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882806539 2000000000 4246756945703 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176561321/400000000 : ℝ)^4223 ≤ (33974058918617/100000000000000 : ℝ)^3199 := by
    have hnat : (176561321 : ℕ)^4223*100000000000000^3199 ≤ 33974058918617^3199*400000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176561321 400000000 33974058918617 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168940981/400000000 : ℝ), (882806539/2000000000 : ℝ), (176561321/400000000 : ℝ)] ![(32051885504607/100000000000000 : ℝ), (4246756945703/12500000000000 : ℝ), (33974058918617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168940981/400000000 : ℝ)|^4223 ≤ (32051885504607/100000000000000 : ℝ)^3199
        have hw : |(168940981/400000000 : ℝ)|=(168940981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882806539/2000000000 : ℝ)|^4223 ≤ (4246756945703/12500000000000 : ℝ)^3199
        have hw : |(882806539/2000000000 : ℝ)|=(882806539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176561321/400000000 : ℝ)|^4223 ≤ (33974058918617/100000000000000 : ℝ)^3199
        have hw : |(176561321/400000000 : ℝ)|=(176561321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2873/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62249/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29693/50000 : ℝ) ∧ (80141/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8337/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2873/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2873/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2873/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2873/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2873/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2873/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2873/25000 : ℝ) ^ (8445/2048 : ℝ) ≤ (13350830894902873/100000000000000000000 : ℝ) := by
    have hpowers : (2873/25000 : ℝ)^8445 ≤ (13350830894902873/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2873 : ℕ)^8445*100000000000000000000^2048 ≤ 13350830894902873^2048*25000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2873 25000 13350830894902873 100000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2873/25000 : ℝ)) (X := (13350830894902873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (8445/2048 : ℝ) ≤ (7780092320162339/25000000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^8445 ≤ (7780092320162339/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1411 : ℕ)^8445*25000000000000000000^2048 ≤ 7780092320162339^2048*10000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 7780092320162339 25000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (7780092320162339/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013350830894902873/50000000000000000000 : ℝ) ≤ (5000323738743947/5000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (50013350830894902873/50000000000000000000 : ℝ)^2048 ≤ (5000323738743947/5000000000000000 : ℝ)^8445 := by
      have hnat : (50013350830894902873 : ℕ)^2048*5000000000000000^8445 ≤ 5000323738743947^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013350830894902873 50000000000000000000 5000323738743947 5000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000323738743947/5000000000000000 : ℝ)) (X := (50013350830894902873/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044471200175552229/100000000000000000000 : ℝ) ≤ (2000215658215837/2000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (100044471200175552229/100000000000000000000 : ℝ)^2048 ≤ (2000215658215837/2000000000000000 : ℝ)^8445 := by
      have hnat : (100044471200175552229 : ℕ)^2048*2000000000000000^8445 ≤ 2000215658215837^8445*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044471200175552229 100000000000000000000 2000215658215837 2000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000215658215837/2000000000000000 : ℝ)) (X := (100044471200175552229/100000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507780092320162339/12500000000000000000 : ℝ) ≤ (2500377276167619/2500000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (12507780092320162339/12500000000000000000 : ℝ)^2048 ≤ (2500377276167619/2500000000000000 : ℝ)^8445 := by
      have hnat : (12507780092320162339 : ℕ)^2048*2500000000000000^8445 ≤ 2500377276167619^8445*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507780092320162339 12500000000000000000 2500377276167619 2500000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500377276167619/2500000000000000 : ℝ)) (X := (12507780092320162339/12500000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13350830894902873/100000000000000000000 : ℝ) ≤ ((384879312889427561/385000000000000000 : ℝ)+2*(430813591291/261800000000000 : ℝ)*(2873/25000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (384879312889427561/385000000000000000 : ℝ)+2*(430813591291/261800000000000 : ℝ)*(2873/25000 : ℝ)=(5000323738743947/5000000000000000 : ℝ) by norm_num, show 1+2*(13350830894902873/100000000000000000000 : ℝ)=(50013350830894902873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7780092320162339/25000000000000000000 : ℝ)+(13350830894902873/100000000000000000000 : ℝ) ≤ ((384879312889427561/385000000000000000 : ℝ)+(430813591291/261800000000000 : ℝ)*((1411/10000 : ℝ)+(2873/25000 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (384879312889427561/385000000000000000 : ℝ)+(430813591291/261800000000000 : ℝ)*((1411/10000 : ℝ)+(2873/25000 : ℝ))=(2000215658215837/2000000000000000 : ℝ) by norm_num, show 1+(7780092320162339/25000000000000000000 : ℝ)+(13350830894902873/100000000000000000000 : ℝ)=(100044471200175552229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7780092320162339/25000000000000000000 : ℝ) ≤ ((384879312889427561/385000000000000000 : ℝ)+2*(430813591291/261800000000000 : ℝ)*(1411/10000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (384879312889427561/385000000000000000 : ℝ)+2*(430813591291/261800000000000 : ℝ)*(1411/10000 : ℝ)=(2500377276167619/2500000000000000 : ℝ) by norm_num, show 1+2*(7780092320162339/25000000000000000000 : ℝ)=(12507780092320162339/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (384879312889427561/385000000000000000 : ℝ)*(X 1 0+X 2 0)+(430813591291/261800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (2873/25000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (384879312889427561/385000000000000000 : ℝ)) (alpha := (430813591291/261800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (384879312889427561/385000000000000000 : ℝ)*(X 0 1+X 2 1)+(430813591291/261800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (2873/25000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (384879312889427561/385000000000000000 : ℝ)) (alpha := (430813591291/261800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (384879312889427561/385000000000000000 : ℝ)*(X 0 2+X 1 2)+(430813591291/261800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (2873/25000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (384879312889427561/385000000000000000 : ℝ)) (alpha := (430813591291/261800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1991552479/10000000000 : ℝ)*X 0 0+(5374676979/10000000000 : ℝ)*X 0 1+(2687339061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((52968699/100000000 : ℝ)*X 1 0+(-1048665093/5000000000 : ℝ)*X 1 1+(2687338669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296869677/10000000000 : ℝ)*X 2 0+(2687338519/5000000000 : ℝ)*X 2 1+(-2097330891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((278480907/625000000 : ℝ)*X 0 0+(4298091519/10000000000 : ℝ)*X 0 1+(67157653/156250000 : ℝ)*X 0 2+(278480907/625000000 : ℝ)*X 1 0+(4298091519/10000000000 : ℝ)*X 1 1+(67157653/156250000 : ℝ)*X 1 2+(278480907/625000000 : ℝ)*X 2 0+(4298091519/10000000000 : ℝ)*X 2 1+(67157653/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2239649273/10000000000 : ℝ)*X 0 0+(1320598607/2500000000 : ℝ)*X 0 1+(5282394433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((167559583/312500000 : ℝ)*X 1 0+(-333429/1562500 : ℝ)*X 1 1+(132059861/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268095333/500000000 : ℝ)*X 2 0+(2641197213/5000000000 : ℝ)*X 2 1+(-2133945613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121218447/5000000000 : ℝ)*X 0 0+(880939887/2000000000 : ℝ)*X 0 1+(68823429/156250000 : ℝ)*X 0 2+(2121218447/5000000000 : ℝ)*X 1 0+(880939887/2000000000 : ℝ)*X 1 1+(68823429/156250000 : ℝ)*X 1 2+(2121218447/5000000000 : ℝ)*X 2 0+(880939887/2000000000 : ℝ)*X 2 1+(68823429/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2187649659/10000000000 : ℝ)*X 0 0+(1043885413/2000000000 : ℝ)*X 0 1+(5384291197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5290091183/10000000000 : ℝ)*X 1 0+(-261681179/1250000000 : ℝ)*X 1 1+(5384290917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2645045479/5000000000 : ℝ)*X 2 0+(5384291419/10000000000 : ℝ)*X 2 1+(-65420283/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2238818527/5000000000 : ℝ)*X 0 0+(2143489411/5000000000 : ℝ)*X 0 1+(857395773/2000000000 : ℝ)*X 0 2+(2238818527/5000000000 : ℝ)*X 1 0+(2143489411/5000000000 : ℝ)*X 1 1+(857395773/2000000000 : ℝ)*X 1 2+(2238818527/5000000000 : ℝ)*X 2 0+(2143489411/5000000000 : ℝ)*X 2 1+(857395773/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2043805487/10000000000 : ℝ)*X 0 0+(5436443461/10000000000 : ℝ)*X 0 1+(5274310917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1341900543/2500000000 : ℝ)*X 1 0+(-2137096841/10000000000 : ℝ)*X 1 1+(1318577621/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2683800979/5000000000 : ℝ)*X 2 0+(5274310559/10000000000 : ℝ)*X 2 1+(-2137097027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((168940981/400000000 : ℝ)*X 0 0+(882806539/2000000000 : ℝ)*X 0 1+(176561321/400000000 : ℝ)*X 0 2+(168940981/400000000 : ℝ)*X 1 0+(882806539/2000000000 : ℝ)*X 1 1+(176561321/400000000 : ℝ)*X 1 2+(168940981/400000000 : ℝ)*X 2 0+(882806539/2000000000 : ℝ)*X 2 1+(176561321/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62249/100000 : ℝ) ≤ (-2995606570971805001760262243287/4812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4685861/100000000000000 : ℝ)*(upper0) + (7985809/100000000000000 : ℝ)*(upper1) + (9518607/100000000000000 : ℝ)*(upper2) + (11765163/100000000000000 : ℝ)*(upper3) + (10088293/50000000000000 : ℝ)*(upper5) + (2006009685434089/50000000000000 : ℝ)*(major0) + (2006009685434089/50000000000000 : ℝ)*(major1) + (2006009685434089/50000000000000 : ℝ)*(major2) + (359126403/20000000000000 : ℝ)*(sp2) + (893768797/50000000000000 : ℝ)*(sp3) + (5399104670693377/100000000000000 : ℝ)*(sp4) + (5399104670693377/100000000000000 : ℝ)*(sp5) + (2699551437530681/50000000000000 : ℝ)*(sp6) + (330710134200909/12500000000000 : ℝ)*(sp7) + (1322841430572433/50000000000000 : ℝ)*(f.failure) + (5399104670693377/100000000000000 : ℝ)*(f.sum) + (176074868757/96250000000000000000000000 : ℝ)*base66 + (35678589970701929/19250000000000000000000000000000 : ℝ)*base67 + (4935847040859951929/19250000000000000000000000000000 : ℝ)*base69 + (21554198035201929/19250000000000000000000000000000 : ℝ)*base71 + (1420110108037/385000000000000000000000000 : ℝ)*base73 + (1226471108309201929/19250000000000000000000000000000 : ℝ)*base75 + (24461664847451929/19250000000000000000000000000000 : ℝ)*base77 + (2913298911229798071/19250000000000000000000000000000 : ℝ)*base80 + (63889933584441/192500000000000000000000000 : ℝ)*base81 + (4501567/2500000000000000000000 : ℝ)*base90 + (4501567/2500000000000000000000 : ℝ)*base92 + (4501567/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29693/50000 : ℝ) ≤ (433815399274889478132951636981/730468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (399760663/100000000000000 : ℝ)*(lower0) + (246148663/100000000000000 : ℝ)*(upper2) + (94318227/25000000000000 : ℝ)*(lower5) + (254876409155279/6250000000000 : ℝ)*(major0) + (254876409155279/6250000000000 : ℝ)*(major1) + (254876409155279/6250000000000 : ℝ)*(major2) + (5447003098052281/100000000000000 : ℝ)*(sp0) + (1089398359279643/20000000000000 : ℝ)*(sp1) + (2723403934186541/50000000000000 : ℝ)*(sp2) + (1344587112927659/50000000000000 : ℝ)*(sp3) + (3371689237/10000000000000 : ℝ)*(sp7) + (49143089611/100000000000000 : ℝ)*(sp9) + (29133889343/12500000000000 : ℝ)*(sp10) + (7568287109/20000000000000 : ℝ)*(sp12) + (336150992843461/12500000000000 : ℝ)*(f.failure) + (2723520469743913/50000000000000 : ℝ)*(f.sum) + (2187846378661/3272500000000000000000000000 : ℝ)*base65 + (852791530727631823/40906250000000000000000000000000 : ℝ)*base67 + (160654251050038073/40906250000000000000000000000000 : ℝ)*base69 + (238603716725850573/40906250000000000000000000000000 : ℝ)*base71 + (125450268362131/3272500000000000000000000000 : ℝ)*base73 + (301360546419100573/40906250000000000000000000000000 : ℝ)*base75 + (91075696179694323/40906250000000000000000000000000 : ℝ)*base77 + (229833828447256823/40906250000000000000000000000000 : ℝ)*base79 + (5069010134131/3272500000000000000000000000 : ℝ)*base81 + (7214539/625000000000000000000 : ℝ)*base90 + (7214539/625000000000000000000 : ℝ)*base92 + (7214539/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80141/100000 : ℝ) ≤ (1498686977790591069568431837/1870000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223860249/100000000000000 : ℝ)*(lower3) + (21736097/25000000000000 : ℝ)*(upper4) + (110884649/100000000000000 : ℝ)*(lower5) + (4544617649473531/100000000000000 : ℝ)*(major0) + (4544617649473531/100000000000000 : ℝ)*(major1) + (4544617649473531/100000000000000 : ℝ)*(major2) + (6676028971/50000000000000 : ℝ)*(sp0) + (69545666901/100000000000000 : ℝ)*(sp1) + (399137234033/100000000000000 : ℝ)*(sp2) + (20420419897/12500000000000 : ℝ)*(sp3) + (1516402084465131/25000000000000 : ℝ)*(sp8) + (1516388036062891/25000000000000 : ℝ)*(sp9) + (6065222552684433/100000000000000 : ℝ)*(sp10) + (1498367841392723/50000000000000 : ℝ)*(sp11) + (1498449523072311/50000000000000 : ℝ)*(f.failure) + (3032810844959233/50000000000000 : ℝ)*(f.sum) + (2276610752437/1870000000000000000000000000 : ℝ)*base66 + (157508611100517021/93500000000000000000000000000000 : ℝ)*base67 + (1177580703249482979/93500000000000000000000000000000 : ℝ)*base70 + (812258996818482979/93500000000000000000000000000000 : ℝ)*base72 + (5884418694637/1870000000000000000000000000 : ℝ)*base74 + (413893869581517021/93500000000000000000000000000000 : ℝ)*base75 + (1046685379838982979/93500000000000000000000000000000 : ℝ)*base78 + (184453870920017021/93500000000000000000000000000000 : ℝ)*base79 + (4557847817467/1870000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12714311/2500000000000000000000 : ℝ)*base89 + (12714311/2500000000000000000000 : ℝ)*base91 + (12714311/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-8337/10000 : ℝ) ≤ (-6200443949413917127910605206441/7437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23819731/100000000000000 : ℝ)*(upper3) + (183121747/100000000000000 : ℝ)*(lower4) + (37067879/100000000000000 : ℝ)*(upper5) + (2290095448132841/50000000000000 : ℝ)*(major0) + (2290095448132841/50000000000000 : ℝ)*(major1) + (2290095448132841/50000000000000 : ℝ)*(major2) + (1375929793/10000000000000 : ℝ)*(sp4) + (373589866027/100000000000000 : ℝ)*(sp5) + (463380924903/100000000000000 : ℝ)*(sp6) + (183170533267/100000000000000 : ℝ)*(sp7) + (1541949924517177/25000000000000 : ℝ)*(sp12) + (6167439867500611/100000000000000 : ℝ)*(sp13) + (1233470015288347/20000000000000 : ℝ)*(sp14) + (755043567291661/25000000000000 : ℝ)*(sp15) + (3020357439699911/100000000000000 : ℝ)*(f.failure) + (3083906728683319/50000000000000 : ℝ)*(f.sum) + (3895169140309/6545000000000000000000000000 : ℝ)*base66 + (2511038207792748617/327250000000000000000000000000000 : ℝ)*base67 + (52655172511498617/327250000000000000000000000000000 : ℝ)*base69 + (215602822607498617/327250000000000000000000000000000 : ℝ)*base71 + (19729417016401/6545000000000000000000000000 : ℝ)*base73 + (1033591407135998617/327250000000000000000000000000000 : ℝ)*base75 + (1956583194468998617/327250000000000000000000000000000 : ℝ)*base77 + (1360760645341001383/327250000000000000000000000000000 : ℝ)*base80 + (2520112785329/6545000000000000000000000000 : ℝ)*base82 + (8458089/5000000000000000000000 : ℝ)*base90 + (8458089/5000000000000000000000 : ℝ)*base92 + (8458089/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1253_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2873/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29693/50000 : ℝ) else (80141/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8337/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1253_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1253_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29693/50000 : ℝ) else (80141/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8337/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1253_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1253_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1253_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29693/50000 : ℝ) else (80141/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8337/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
