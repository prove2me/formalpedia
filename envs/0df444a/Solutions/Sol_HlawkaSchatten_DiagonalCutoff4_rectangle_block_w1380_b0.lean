-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:52.76314+00:00
-- url     : https://prove2.me/submissions/7dc6a022-d0cc-4ebf-8244-cde90d9ac3de

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
theorem support_rectangle_w1380_s0_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1786893271/10000000000 : ℝ)*x 0 + (5980665807/10000000000 : ℝ)*x 1 + (4819894137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1786893271/10000000000 : ℝ)^1085 ≤ (65617903743/625000000000 : ℝ)^829 := by
    have hnat : (1786893271 : ℕ)^1085*625000000000^829 ≤ 65617903743^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786893271 10000000000 65617903743 625000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5980665807/10000000000 : ℝ)^1085 ≤ (12756998594823/25000000000000 : ℝ)^829 := by
    have hnat : (5980665807 : ℕ)^1085*25000000000000^829 ≤ 12756998594823^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5980665807 10000000000 12756998594823 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4819894137/10000000000 : ℝ)^1085 ≤ (19236570503657/50000000000000 : ℝ)^829 := by
    have hnat : (4819894137 : ℕ)^1085*50000000000000^829 ≤ 19236570503657^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819894137 10000000000 19236570503657 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1786893271/10000000000 : ℝ), (5980665807/10000000000 : ℝ), (4819894137/10000000000 : ℝ)] ![(65617903743/625000000000 : ℝ), (12756998594823/25000000000000 : ℝ), (19236570503657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1786893271/10000000000 : ℝ)|^1085 ≤ (65617903743/625000000000 : ℝ)^829
        have hw : |(-1786893271/10000000000 : ℝ)|=(1786893271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5980665807/10000000000 : ℝ)|^1085 ≤ (12756998594823/25000000000000 : ℝ)^829
        have hw : |(5980665807/10000000000 : ℝ)|=(5980665807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4819894137/10000000000 : ℝ)|^1085 ≤ (19236570503657/50000000000000 : ℝ)^829
        have hw : |(4819894137/10000000000 : ℝ)|=(4819894137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s0_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5497562321/10000000000 : ℝ)*x 0 + (-611217319/2500000000 : ℝ)*x 1 + (2409947401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497562321/10000000000 : ℝ)^1085 ≤ (5712723647863/12500000000000 : ℝ)^829 := by
    have hnat : (5497562321 : ℕ)^1085*12500000000000^829 ≤ 5712723647863^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497562321 10000000000 5712723647863 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611217319/2500000000 : ℝ)^1085 ≤ (791253142259/5000000000000 : ℝ)^829 := by
    have hnat : (611217319 : ℕ)^1085*5000000000000^829 ≤ 791253142259^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611217319 2500000000 791253142259 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2409947401/5000000000 : ℝ)^1085 ≤ (38473147954629/100000000000000 : ℝ)^829 := by
    have hnat : (2409947401 : ℕ)^1085*100000000000000^829 ≤ 38473147954629^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409947401 5000000000 38473147954629 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497562321/10000000000 : ℝ), (-611217319/2500000000 : ℝ), (2409947401/5000000000 : ℝ)] ![(5712723647863/12500000000000 : ℝ), (791253142259/5000000000000 : ℝ), (38473147954629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497562321/10000000000 : ℝ)|^1085 ≤ (5712723647863/12500000000000 : ℝ)^829
        have hw : |(5497562321/10000000000 : ℝ)|=(5497562321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-611217319/2500000000 : ℝ)|^1085 ≤ (791253142259/5000000000000 : ℝ)^829
        have hw : |(-611217319/2500000000 : ℝ)|=(611217319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2409947401/5000000000 : ℝ)|^1085 ≤ (38473147954629/100000000000000 : ℝ)^829
        have hw : |(2409947401/5000000000 : ℝ)|=(2409947401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s0_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5497562189/10000000000 : ℝ)*x 0 + (1204973509/2500000000 : ℝ)*x 1 + (-2444870391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497562189/10000000000 : ℝ)^1085 ≤ (45701787746713/100000000000000 : ℝ)^829 := by
    have hnat : (5497562189 : ℕ)^1085*100000000000000^829 ≤ 45701787746713^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497562189 10000000000 45701787746713 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204973509/2500000000 : ℝ)^1085 ≤ (19236569976079/50000000000000 : ℝ)^829 := by
    have hnat : (1204973509 : ℕ)^1085*50000000000000^829 ≤ 19236569976079^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204973509 2500000000 19236569976079 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2444870391/10000000000 : ℝ)^1085 ≤ (3165014458201/20000000000000 : ℝ)^829 := by
    have hnat : (2444870391 : ℕ)^1085*20000000000000^829 ≤ 3165014458201^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2444870391 10000000000 3165014458201 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497562189/10000000000 : ℝ), (1204973509/2500000000 : ℝ), (-2444870391/10000000000 : ℝ)] ![(45701787746713/100000000000000 : ℝ), (19236569976079/50000000000000 : ℝ), (3165014458201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497562189/10000000000 : ℝ)|^1085 ≤ (45701787746713/100000000000000 : ℝ)^829
        have hw : |(5497562189/10000000000 : ℝ)|=(5497562189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204973509/2500000000 : ℝ)|^1085 ≤ (19236569976079/50000000000000 : ℝ)^829
        have hw : |(1204973509/2500000000 : ℝ)|=(1204973509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2444870391/10000000000 : ℝ)|^1085 ≤ (3165014458201/20000000000000 : ℝ)^829
        have hw : |(-2444870391/10000000000 : ℝ)|=(2444870391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s0_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2086556659/5000000000 : ℝ)*x 0 + (1552447809/5000000000 : ℝ)*x 1 + (2785510707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086556659/5000000000 : ℝ)^1085 ≤ (7965189119971/25000000000000 : ℝ)^829 := by
    have hnat : (2086556659 : ℕ)^1085*25000000000000^829 ≤ 7965189119971^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086556659 5000000000 7965189119971 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552447809/5000000000 : ℝ)^1085 ≤ (10818279125781/50000000000000 : ℝ)^829 := by
    have hnat : (1552447809 : ℕ)^1085*50000000000000^829 ≤ 10818279125781^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552447809 5000000000 10818279125781 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2785510707/5000000000 : ℝ)^1085 ≤ (46502685257597/100000000000000 : ℝ)^829 := by
    have hnat : (2785510707 : ℕ)^1085*100000000000000^829 ≤ 46502685257597^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785510707 5000000000 46502685257597 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086556659/5000000000 : ℝ), (1552447809/5000000000 : ℝ), (2785510707/5000000000 : ℝ)] ![(7965189119971/25000000000000 : ℝ), (10818279125781/50000000000000 : ℝ), (46502685257597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086556659/5000000000 : ℝ)|^1085 ≤ (7965189119971/25000000000000 : ℝ)^829
        have hw : |(2086556659/5000000000 : ℝ)|=(2086556659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552447809/5000000000 : ℝ)|^1085 ≤ (10818279125781/50000000000000 : ℝ)^829
        have hw : |(1552447809/5000000000 : ℝ)|=(1552447809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2785510707/5000000000 : ℝ)|^1085 ≤ (46502685257597/100000000000000 : ℝ)^829
        have hw : |(2785510707/5000000000 : ℝ)|=(2785510707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s0_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-447788657/2500000000 : ℝ)*x 0 + (4849697933/10000000000 : ℝ)*x 1 + (1189959291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447788657/2500000000 : ℝ)^1085 ≤ (5265822967319/50000000000000 : ℝ)^829 := by
    have hnat : (447788657 : ℕ)^1085*50000000000000^829 ≤ 5265822967319^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447788657 2500000000 5265822967319 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4849697933/10000000000 : ℝ)^1085 ≤ (38784800809323/100000000000000 : ℝ)^829 := by
    have hnat : (4849697933 : ℕ)^1085*100000000000000^829 ≤ 38784800809323^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849697933 10000000000 38784800809323 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1189959291/2000000000 : ℝ)^1085 ≤ (12670888309261/25000000000000 : ℝ)^829 := by
    have hnat : (1189959291 : ℕ)^1085*25000000000000^829 ≤ 12670888309261^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189959291 2000000000 12670888309261 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-447788657/2500000000 : ℝ), (4849697933/10000000000 : ℝ), (1189959291/2000000000 : ℝ)] ![(5265822967319/50000000000000 : ℝ), (38784800809323/100000000000000 : ℝ), (12670888309261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-447788657/2500000000 : ℝ)|^1085 ≤ (5265822967319/50000000000000 : ℝ)^829
        have hw : |(-447788657/2500000000 : ℝ)|=(447788657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4849697933/10000000000 : ℝ)|^1085 ≤ (38784800809323/100000000000000 : ℝ)^829
        have hw : |(4849697933/10000000000 : ℝ)|=(4849697933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1189959291/2000000000 : ℝ)|^1085 ≤ (12670888309261/25000000000000 : ℝ)^829
        have hw : |(1189959291/2000000000 : ℝ)|=(1189959291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s0_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1036198203/2000000000 : ℝ)*x 0 + (-657485033/5000000000 : ℝ)*x 1 + (5949794927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036198203/2000000000 : ℝ)^1085 ≤ (5286057504117/12500000000000 : ℝ)^829 := by
    have hnat : (1036198203 : ℕ)^1085*12500000000000^829 ≤ 5286057504117^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036198203 2000000000 5286057504117 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657485033/5000000000 : ℝ)^1085 ≤ (7028003752377/100000000000000 : ℝ)^829 := by
    have hnat : (657485033 : ℕ)^1085*100000000000000^829 ≤ 7028003752377^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657485033 5000000000 7028003752377 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5949794927/10000000000 : ℝ)^1085 ≤ (25341768100603/50000000000000 : ℝ)^829 := by
    have hnat : (5949794927 : ℕ)^1085*50000000000000^829 ≤ 25341768100603^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5949794927 10000000000 25341768100603 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036198203/2000000000 : ℝ), (-657485033/5000000000 : ℝ), (5949794927/10000000000 : ℝ)] ![(5286057504117/12500000000000 : ℝ), (7028003752377/100000000000000 : ℝ), (25341768100603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036198203/2000000000 : ℝ)|^1085 ≤ (5286057504117/12500000000000 : ℝ)^829
        have hw : |(1036198203/2000000000 : ℝ)|=(1036198203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-657485033/5000000000 : ℝ)|^1085 ≤ (7028003752377/100000000000000 : ℝ)^829
        have hw : |(-657485033/5000000000 : ℝ)|=(657485033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5949794927/10000000000 : ℝ)|^1085 ≤ (25341768100603/50000000000000 : ℝ)^829
        have hw : |(5949794927/10000000000 : ℝ)|=(5949794927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s0_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1036197783/2000000000 : ℝ)*x 0 + (5949798553/10000000000 : ℝ)*x 1 + (-1314967493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036197783/2000000000 : ℝ)^1085 ≤ (21144218799551/50000000000000 : ℝ)^829 := by
    have hnat : (1036197783 : ℕ)^1085*50000000000000^829 ≤ 21144218799551^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036197783 2000000000 21144218799551 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5949798553/10000000000 : ℝ)^1085 ≤ (405468613023/800000000000 : ℝ)^829 := by
    have hnat : (5949798553 : ℕ)^1085*800000000000^829 ≤ 405468613023^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5949798553 10000000000 405468613023 800000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314967493/10000000000 : ℝ)^1085 ≤ (3513992877049/50000000000000 : ℝ)^829 := by
    have hnat : (1314967493 : ℕ)^1085*50000000000000^829 ≤ 3513992877049^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314967493 10000000000 3513992877049 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036197783/2000000000 : ℝ), (5949798553/10000000000 : ℝ), (-1314967493/10000000000 : ℝ)] ![(21144218799551/50000000000000 : ℝ), (405468613023/800000000000 : ℝ), (3513992877049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036197783/2000000000 : ℝ)|^1085 ≤ (21144218799551/50000000000000 : ℝ)^829
        have hw : |(1036197783/2000000000 : ℝ)|=(1036197783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5949798553/10000000000 : ℝ)|^1085 ≤ (405468613023/800000000000 : ℝ)^829
        have hw : |(5949798553/10000000000 : ℝ)|=(5949798553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1314967493/10000000000 : ℝ)|^1085 ≤ (3513992877049/50000000000000 : ℝ)^829
        have hw : |(-1314967493/10000000000 : ℝ)|=(1314967493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s0_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4182156663/10000000000 : ℝ)*x 0 + (5507704897/10000000000 : ℝ)*x 1 + (63409633/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182156663/10000000000 : ℝ)^1085 ≤ (31951151692363/100000000000000 : ℝ)^829 := by
    have hnat : (4182156663 : ℕ)^1085*100000000000000^829 ≤ 31951151692363^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182156663 10000000000 31951151692363 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507704897/10000000000 : ℝ)^1085 ≤ (45812174208629/100000000000000 : ℝ)^829 := by
    have hnat : (5507704897 : ℕ)^1085*100000000000000^829 ≤ 45812174208629^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507704897 10000000000 45812174208629 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63409633/200000000 : ℝ)^1085 ≤ (1389792130017/6250000000000 : ℝ)^829 := by
    have hnat : (63409633 : ℕ)^1085*6250000000000^829 ≤ 1389792130017^829*200000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63409633 200000000 1389792130017 6250000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182156663/10000000000 : ℝ), (5507704897/10000000000 : ℝ), (63409633/200000000 : ℝ)] ![(31951151692363/100000000000000 : ℝ), (45812174208629/100000000000000 : ℝ), (1389792130017/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182156663/10000000000 : ℝ)|^1085 ≤ (31951151692363/100000000000000 : ℝ)^829
        have hw : |(4182156663/10000000000 : ℝ)|=(4182156663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507704897/10000000000 : ℝ)|^1085 ≤ (45812174208629/100000000000000 : ℝ)^829
        have hw : |(5507704897/10000000000 : ℝ)|=(5507704897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63409633/200000000 : ℝ)|^1085 ≤ (1389792130017/6250000000000 : ℝ)^829
        have hw : |(63409633/200000000 : ℝ)|=(63409633/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (53/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (133/500 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4339/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4339 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4339*1^1024 ≤ 0^1024*1^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4339/1024 : ℝ) ≤ (2059714071046455739/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4339 ≤ (2059714071046455739/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4339*100000000000000000000^1024 ≤ 2059714071046455739^1024*5^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2059714071046455739 100000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2059714071046455739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4339 := by
      have hnat : (1 : ℕ)^1024*1^4339 ≤ 1^4339*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102059714071046455739/100000000000000000000 : ℝ) ≤ (5024115583759663/5000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (102059714071046455739/100000000000000000000 : ℝ)^1024 ≤ (5024115583759663/5000000000000000 : ℝ)^4339 := by
      have hnat : (102059714071046455739 : ℕ)^1024*5000000000000000^4339 ≤ 5024115583759663^4339*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102059714071046455739 100000000000000000000 5024115583759663 5000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024115583759663/5000000000000000 : ℝ)) (X := (102059714071046455739/100000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52059714071046455739/50000000000000000000 : ℝ) ≤ (2524115583759663/2500000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (52059714071046455739/50000000000000000000 : ℝ)^1024 ≤ (2524115583759663/2500000000000000 : ℝ)^4339 := by
      have hnat : (52059714071046455739 : ℕ)^1024*2500000000000000^4339 ≤ 2524115583759663^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52059714071046455739 50000000000000000000 2524115583759663 2500000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2524115583759663/2500000000000000 : ℝ)) (X := (52059714071046455739/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(24115583759663/2000000000000000 : ℝ)*(0 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24115583759663/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2059714071046455739/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(24115583759663/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (1 : ℝ)+(24115583759663/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5024115583759663/5000000000000000 : ℝ) by norm_num, show 1+(2059714071046455739/100000000000000000000 : ℝ)+(0 : ℝ)=(102059714071046455739/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2059714071046455739/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(24115583759663/2000000000000000 : ℝ)*(2/5 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24115583759663/2000000000000000 : ℝ)*(2/5 : ℝ)=(2524115583759663/2500000000000000 : ℝ) by norm_num, show 1+2*(2059714071046455739/100000000000000000000 : ℝ)=(52059714071046455739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(24115583759663/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24115583759663/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(24115583759663/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24115583759663/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(24115583759663/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24115583759663/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1786893271/10000000000 : ℝ)*X 0 0+(5980665807/10000000000 : ℝ)*X 0 1+(4819894137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5497562321/10000000000 : ℝ)*X 1 0+(-611217319/2500000000 : ℝ)*X 1 1+(2409947401/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5497562189/10000000000 : ℝ)*X 2 0+(1204973509/2500000000 : ℝ)*X 2 1+(-2444870391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2086556659/5000000000 : ℝ)*X 0 0+(1552447809/5000000000 : ℝ)*X 0 1+(2785510707/5000000000 : ℝ)*X 0 2+(2086556659/5000000000 : ℝ)*X 1 0+(1552447809/5000000000 : ℝ)*X 1 1+(2785510707/5000000000 : ℝ)*X 1 2+(2086556659/5000000000 : ℝ)*X 2 0+(1552447809/5000000000 : ℝ)*X 2 1+(2785510707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-447788657/2500000000 : ℝ)*X 0 0+(4849697933/10000000000 : ℝ)*X 0 1+(1189959291/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036198203/2000000000 : ℝ)*X 1 0+(-657485033/5000000000 : ℝ)*X 1 1+(5949794927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1036197783/2000000000 : ℝ)*X 2 0+(5949798553/10000000000 : ℝ)*X 2 1+(-1314967493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4182156663/10000000000 : ℝ)*X 0 0+(5507704897/10000000000 : ℝ)*X 0 1+(63409633/200000000 : ℝ)*X 0 2+(4182156663/10000000000 : ℝ)*X 1 0+(5507704897/10000000000 : ℝ)*X 1 1+(63409633/200000000 : ℝ)*X 1 2+(4182156663/10000000000 : ℝ)*X 2 0+(5507704897/10000000000 : ℝ)*X 2 1+(63409633/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (256856292063029250226551/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26658003/12500000000000 : ℝ)*(base1) + (34431713/50000000000000 : ℝ)*(base16) + (106222243/20000000000000 : ℝ)*(base19) + (289644763/50000000000000 : ℝ)*(base23) + (66822059/100000000000000 : ℝ)*(upper3) + (633496966524141/100000000000000 : ℝ)*(major0) + (633496966524141/100000000000000 : ℝ)*(major1) + (633496966524141/100000000000000 : ℝ)*(major2) + (430748732725829/50000000000000 : ℝ)*(sp0) + (21537444981771/2500000000000 : ℝ)*(sp1) + (172299563991191/20000000000000 : ℝ)*(sp2) + (101373673162939/25000000000000 : ℝ)*(sp3) + (1147057847/100000000000000 : ℝ)*(sp4) + (542268253/100000000000000 : ℝ)*(sp7) + (202747724092017/50000000000000 : ℝ)*(f.failure) + (861498399245481/100000000000000 : ℝ)*(f.sum) + (27545140224483/100000000000000000000000000000 : ℝ)*base65 + (353964150324483/200000000000000000000000000000 : ℝ)*base67 + (380585438524483/200000000000000000000000000000 : ℝ)*base69 + (325135325875517/200000000000000000000000000000 : ℝ)*base72 + (112272999375517/100000000000000000000000000000 : ℝ)*base74 + (198316991275517/200000000000000000000000000000 : ℝ)*base76 + (355791503124483/200000000000000000000000000000 : ℝ)*base77 + (615595074275517/200000000000000000000000000000 : ℝ)*base80 + (16756628624483/100000000000000000000000000000 : ℝ)*base81 + (17693031/2500000000000000000000 : ℝ)*base89 + (17693031/2500000000000000000000 : ℝ)*base91 + (17693031/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5308989833395416573/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92862937/20000000000000 : ℝ)*(base19) + (167336359/20000000000000 : ℝ)*(base23) + (62869773/100000000000000 : ℝ)*(base39) + (272755979/100000000000000 : ℝ)*(upper2) + (45011761/50000000000000 : ℝ)*(upper5) + (668433071110871/100000000000000 : ℝ)*(major0) + (668433071110871/100000000000000 : ℝ)*(major1) + (668433008241097/100000000000000 : ℝ)*(major2) + (435087293/100000000000000 : ℝ)*(sp1) + (1469131511/50000000000000 : ℝ)*(sp2) + (181801636468541/20000000000000 : ℝ)*(sp4) + (909007282940727/100000000000000 : ℝ)*(sp5) + (454502235133831/50000000000000 : ℝ)*(sp6) + (106964430010733/25000000000000 : ℝ)*(sp7) + (106964430010733/25000000000000 : ℝ)*(f.failure) + (454504122606239/50000000000000 : ℝ)*(f.sum) + (3548208214587/6250000000000000000000000000 : ℝ)*base65 + (149499346329689/200000000000000000000000000000 : ℝ)*base68 + (559624403527/200000000000000000000000000000 : ℝ)*base70 + (799631832670311/200000000000000000000000000000 : ℝ)*base71 + (30005435397913/6250000000000000000000000000 : ℝ)*base74 + (658386052403527/200000000000000000000000000000 : ℝ)*base76 + (644122529796473/200000000000000000000000000000 : ℝ)*base77 + (706911485803527/200000000000000000000000000000 : ℝ)*base80 + (71791607396473/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (549781/1250000000000000000000 : ℝ)*base90 + (549781/1250000000000000000000 : ℝ)*base92 + (11950219/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1380_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (53/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (133/500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1380_s1_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966241681/10000000000 : ℝ)*x 0 + (5625492587/10000000000 : ℝ)*x 1 + (5060166907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966241681/10000000000 : ℝ)^1085 ≤ (2974732313557/25000000000000 : ℝ)^829 := by
    have hnat : (1966241681 : ℕ)^1085*25000000000000^829 ≤ 2974732313557^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966241681 10000000000 2974732313557 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5625492587/10000000000 : ℝ)^1085 ≤ (47098675055031/100000000000000 : ℝ)^829 := by
    have hnat : (5625492587 : ℕ)^1085*100000000000000^829 ≤ 47098675055031^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625492587 10000000000 47098675055031 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5060166907/10000000000 : ℝ)^1085 ≤ (41002395682883/100000000000000 : ℝ)^829 := by
    have hnat : (5060166907 : ℕ)^1085*100000000000000^829 ≤ 41002395682883^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060166907 10000000000 41002395682883 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966241681/10000000000 : ℝ), (5625492587/10000000000 : ℝ), (5060166907/10000000000 : ℝ)] ![(2974732313557/25000000000000 : ℝ), (47098675055031/100000000000000 : ℝ), (41002395682883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966241681/10000000000 : ℝ)|^1085 ≤ (2974732313557/25000000000000 : ℝ)^829
        have hw : |(-1966241681/10000000000 : ℝ)|=(1966241681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5625492587/10000000000 : ℝ)|^1085 ≤ (47098675055031/100000000000000 : ℝ)^829
        have hw : |(5625492587/10000000000 : ℝ)|=(5625492587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5060166907/10000000000 : ℝ)|^1085 ≤ (41002395682883/100000000000000 : ℝ)^829
        have hw : |(5060166907/10000000000 : ℝ)|=(5060166907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s1_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1350445713/2500000000 : ℝ)*x 0 + (-2266956761/10000000000 : ℝ)*x 1 + (2530084167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350445713/2500000000 : ℝ)^1085 ≤ (44662500744537/100000000000000 : ℝ)^829 := by
    have hnat : (1350445713 : ℕ)^1085*100000000000000^829 ≤ 44662500744537^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350445713 2500000000 44662500744537 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266956761/10000000000 : ℝ)^1085 ≤ (3583772105173/25000000000000 : ℝ)^829 := by
    have hnat : (2266956761 : ℕ)^1085*25000000000000^829 ≤ 3583772105173^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266956761 10000000000 3583772105173 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2530084167/5000000000 : ℝ)^1085 ≤ (4100241081653/10000000000000 : ℝ)^829 := by
    have hnat : (2530084167 : ℕ)^1085*10000000000000^829 ≤ 4100241081653^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530084167 5000000000 4100241081653 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350445713/2500000000 : ℝ), (-2266956761/10000000000 : ℝ), (2530084167/5000000000 : ℝ)] ![(44662500744537/100000000000000 : ℝ), (3583772105173/25000000000000 : ℝ), (4100241081653/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350445713/2500000000 : ℝ)|^1085 ≤ (44662500744537/100000000000000 : ℝ)^829
        have hw : |(1350445713/2500000000 : ℝ)|=(1350445713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2266956761/10000000000 : ℝ)|^1085 ≤ (3583772105173/25000000000000 : ℝ)^829
        have hw : |(-2266956761/10000000000 : ℝ)|=(2266956761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2530084167/5000000000 : ℝ)|^1085 ≤ (4100241081653/10000000000000 : ℝ)^829
        have hw : |(2530084167/5000000000 : ℝ)|=(2530084167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s1_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1350445881/2500000000 : ℝ)*x 0 + (5060167093/10000000000 : ℝ)*x 1 + (-2266957473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350445881/2500000000 : ℝ)^1085 ≤ (44662508016479/100000000000000 : ℝ)^829 := by
    have hnat : (1350445881 : ℕ)^1085*100000000000000^829 ≤ 44662508016479^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350445881 2500000000 44662508016479 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5060167093/10000000000 : ℝ)^1085 ≤ (20501198827727/50000000000000 : ℝ)^829 := by
    have hnat : (5060167093 : ℕ)^1085*50000000000000^829 ≤ 20501198827727^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060167093 10000000000 20501198827727 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266957473/10000000000 : ℝ)^1085 ≤ (2867018862673/20000000000000 : ℝ)^829 := by
    have hnat : (2266957473 : ℕ)^1085*20000000000000^829 ≤ 2867018862673^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266957473 10000000000 2867018862673 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350445881/2500000000 : ℝ), (5060167093/10000000000 : ℝ), (-2266957473/10000000000 : ℝ)] ![(44662508016479/100000000000000 : ℝ), (20501198827727/50000000000000 : ℝ), (2867018862673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350445881/2500000000 : ℝ)|^1085 ≤ (44662508016479/100000000000000 : ℝ)^829
        have hw : |(1350445881/2500000000 : ℝ)|=(1350445881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5060167093/10000000000 : ℝ)|^1085 ≤ (20501198827727/50000000000000 : ℝ)^829
        have hw : |(5060167093/10000000000 : ℝ)|=(5060167093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266957473/10000000000 : ℝ)|^1085 ≤ (2867018862673/20000000000000 : ℝ)^829
        have hw : |(-2266957473/10000000000 : ℝ)|=(2266957473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s1_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (214275193/500000000 : ℝ)*x 0 + (744665993/2000000000 : ℝ)*x 1 + (1231098029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214275193/500000000 : ℝ)^1085 ≤ (32988452543249/100000000000000 : ℝ)^829 := by
    have hnat : (214275193 : ℕ)^1085*100000000000000^829 ≤ 32988452543249^829*500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214275193 500000000 32988452543249 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744665993/2000000000 : ℝ)^1085 ≤ (27443070179903/100000000000000 : ℝ)^829 := by
    have hnat : (744665993 : ℕ)^1085*100000000000000^829 ≤ 27443070179903^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744665993 2000000000 27443070179903 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231098029/2500000000 : ℝ)^1085 ≤ (1978423862963/5000000000000 : ℝ)^829 := by
    have hnat : (1231098029 : ℕ)^1085*5000000000000^829 ≤ 1978423862963^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231098029 2500000000 1978423862963 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214275193/500000000 : ℝ), (744665993/2000000000 : ℝ), (1231098029/2500000000 : ℝ)] ![(32988452543249/100000000000000 : ℝ), (27443070179903/100000000000000 : ℝ), (1978423862963/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214275193/500000000 : ℝ)|^1085 ≤ (32988452543249/100000000000000 : ℝ)^829
        have hw : |(214275193/500000000 : ℝ)|=(214275193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744665993/2000000000 : ℝ)|^1085 ≤ (27443070179903/100000000000000 : ℝ)^829
        have hw : |(744665993/2000000000 : ℝ)|=(744665993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1231098029/2500000000 : ℝ)|^1085 ≤ (1978423862963/5000000000000 : ℝ)^829
        have hw : |(1231098029/2500000000 : ℝ)|=(1231098029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s1_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966712773/10000000000 : ℝ)*x 0 + (5067055383/10000000000 : ℝ)*x 1 + (1404620621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966712773/10000000000 : ℝ)^1085 ≤ (11902660621397/100000000000000 : ℝ)^829 := by
    have hnat : (1966712773 : ℕ)^1085*100000000000000^829 ≤ 11902660621397^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966712773 10000000000 11902660621397 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5067055383/10000000000 : ℝ)^1085 ≤ (41075464822583/100000000000000 : ℝ)^829 := by
    have hnat : (5067055383 : ℕ)^1085*100000000000000^829 ≤ 41075464822583^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067055383 10000000000 41075464822583 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1404620621/2500000000 : ℝ)^1085 ≤ (2351093726871/5000000000000 : ℝ)^829 := by
    have hnat : (1404620621 : ℕ)^1085*5000000000000^829 ≤ 2351093726871^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404620621 2500000000 2351093726871 5000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966712773/10000000000 : ℝ), (5067055383/10000000000 : ℝ), (1404620621/2500000000 : ℝ)] ![(11902660621397/100000000000000 : ℝ), (41075464822583/100000000000000 : ℝ), (2351093726871/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966712773/10000000000 : ℝ)|^1085 ≤ (11902660621397/100000000000000 : ℝ)^829
        have hw : |(-1966712773/10000000000 : ℝ)|=(1966712773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5067055383/10000000000 : ℝ)|^1085 ≤ (41075464822583/100000000000000 : ℝ)^829
        have hw : |(5067055383/10000000000 : ℝ)|=(5067055383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1404620621/2500000000 : ℝ)|^1085 ≤ (2351093726871/5000000000000 : ℝ)^829
        have hw : |(1404620621/2500000000 : ℝ)|=(1404620621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s1_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5254633601/10000000000 : ℝ)*x 0 + (-854321191/5000000000 : ℝ)*x 1 + (5618482571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254633601/10000000000 : ℝ)^1085 ≤ (10769222111723/25000000000000 : ℝ)^829 := by
    have hnat : (5254633601 : ℕ)^1085*25000000000000^829 ≤ 10769222111723^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254633601 10000000000 10769222111723 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854321191/5000000000 : ℝ)^1085 ≤ (2475309011851/25000000000000 : ℝ)^829 := by
    have hnat : (854321191 : ℕ)^1085*25000000000000^829 ≤ 2475309011851^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854321191 5000000000 2475309011851 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5618482571/10000000000 : ℝ)^1085 ≤ (47021875490381/100000000000000 : ℝ)^829 := by
    have hnat : (5618482571 : ℕ)^1085*100000000000000^829 ≤ 47021875490381^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618482571 10000000000 47021875490381 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254633601/10000000000 : ℝ), (-854321191/5000000000 : ℝ), (5618482571/10000000000 : ℝ)] ![(10769222111723/25000000000000 : ℝ), (2475309011851/25000000000000 : ℝ), (47021875490381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254633601/10000000000 : ℝ)|^1085 ≤ (10769222111723/25000000000000 : ℝ)^829
        have hw : |(5254633601/10000000000 : ℝ)|=(5254633601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854321191/5000000000 : ℝ)|^1085 ≤ (2475309011851/25000000000000 : ℝ)^829
        have hw : |(-854321191/5000000000 : ℝ)|=(854321191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5618482571/10000000000 : ℝ)|^1085 ≤ (47021875490381/100000000000000 : ℝ)^829
        have hw : |(5618482571/10000000000 : ℝ)|=(5618482571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s1_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5254633913/10000000000 : ℝ)*x 0 + (1404620717/2500000000 : ℝ)*x 1 + (-1708641511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254633913/10000000000 : ℝ)^1085 ≤ (21538445897239/50000000000000 : ℝ)^829 := by
    have hnat : (5254633913 : ℕ)^1085*50000000000000^829 ≤ 21538445897239^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254633913 10000000000 21538445897239 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404620717/2500000000 : ℝ)^1085 ≤ (9404375748719/20000000000000 : ℝ)^829 := by
    have hnat : (1404620717 : ℕ)^1085*20000000000000^829 ≤ 9404375748719^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404620717 2500000000 9404375748719 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1708641511/10000000000 : ℝ)^1085 ≤ (9901229441511/100000000000000 : ℝ)^829 := by
    have hnat : (1708641511 : ℕ)^1085*100000000000000^829 ≤ 9901229441511^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708641511 10000000000 9901229441511 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254633913/10000000000 : ℝ), (1404620717/2500000000 : ℝ), (-1708641511/10000000000 : ℝ)] ![(21538445897239/50000000000000 : ℝ), (9404375748719/20000000000000 : ℝ), (9901229441511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254633913/10000000000 : ℝ)|^1085 ≤ (21538445897239/50000000000000 : ℝ)^829
        have hw : |(5254633913/10000000000 : ℝ)|=(5254633913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1404620717/2500000000 : ℝ)|^1085 ≤ (9404375748719/20000000000000 : ℝ)^829
        have hw : |(1404620717/2500000000 : ℝ)|=(1404620717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1708641511/10000000000 : ℝ)|^1085 ≤ (9901229441511/100000000000000 : ℝ)^829
        have hw : |(-1708641511/10000000000 : ℝ)|=(1708641511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s1_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4286506209/10000000000 : ℝ)*x 0 + (76714973/156250000 : ℝ)*x 1 + (467277501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286506209/10000000000 : ℝ)^1085 ≤ (32998551346357/100000000000000 : ℝ)^829 := by
    have hnat : (4286506209 : ℕ)^1085*100000000000000^829 ≤ 32998551346357^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286506209 10000000000 32998551346357 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76714973/156250000 : ℝ)^1085 ≤ (7882930171267/20000000000000 : ℝ)^829 := by
    have hnat : (76714973 : ℕ)^1085*20000000000000^829 ≤ 7882930171267^829*156250000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76714973 156250000 7882930171267 20000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467277501/1250000000 : ℝ)^1085 ≤ (2758679777779/10000000000000 : ℝ)^829 := by
    have hnat : (467277501 : ℕ)^1085*10000000000000^829 ≤ 2758679777779^829*1250000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467277501 1250000000 2758679777779 10000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286506209/10000000000 : ℝ), (76714973/156250000 : ℝ), (467277501/1250000000 : ℝ)] ![(32998551346357/100000000000000 : ℝ), (7882930171267/20000000000000 : ℝ), (2758679777779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286506209/10000000000 : ℝ)|^1085 ≤ (32998551346357/100000000000000 : ℝ)^829
        have hw : |(4286506209/10000000000 : ℝ)|=(4286506209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(76714973/156250000 : ℝ)|^1085 ≤ (7882930171267/20000000000000 : ℝ)^829
        have hw : |(76714973/156250000 : ℝ)|=(76714973/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467277501/1250000000 : ℝ)|^1085 ≤ (2758679777779/10000000000000 : ℝ)^829
        have hw : |(467277501/1250000000 : ℝ)|=(467277501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (133/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (53/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (3617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19183/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (133/500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (53/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (133/500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (53/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (133/500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (53/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (133/500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (53/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (133/500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (53/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (133/500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (53/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (53/3125 : ℝ) ^ (4339/1024 : ℝ) ≤ (3144400421559/100000000000000000000 : ℝ) := by
    have hpowers : (53/3125 : ℝ)^4339 ≤ (3144400421559/100000000000000000000 : ℝ)^1024 := by
      have hnat : (53 : ℕ)^4339*100000000000000000000^1024 ≤ 3144400421559^1024*3125^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53 3125 3144400421559 100000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (53/3125 : ℝ)) (X := (3144400421559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (133/500 : ℝ) ^ (4339/1024 : ℝ) ≤ (91408855580506799/25000000000000000000 : ℝ) := by
    have hpowers : (133/500 : ℝ)^4339 ≤ (91408855580506799/25000000000000000000 : ℝ)^1024 := by
      have hnat : (133 : ℕ)^4339*25000000000000000000^1024 ≤ 91408855580506799^1024*500^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133 500 91408855580506799 25000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (133/500 : ℝ)) (X := (91408855580506799/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003144400421559/50000000000000000000 : ℝ) ≤ (10000000148415117/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50000003144400421559/50000000000000000000 : ℝ)^1024 ≤ (10000000148415117/10000000000000000 : ℝ)^4339 := by
      have hnat : (50000003144400421559 : ℕ)^1024*10000000000000000^4339 ≤ 10000000148415117^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003144400421559 50000000000000000000 10000000148415117 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000148415117/10000000000000000 : ℝ)) (X := (50000003144400421559/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20073127713344489751/20000000000000000000 : ℝ) ≤ (250215425244637/250000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (20073127713344489751/20000000000000000000 : ℝ)^1024 ≤ (250215425244637/250000000000000 : ℝ)^4339 := by
      have hnat : (20073127713344489751 : ℕ)^1024*250000000000000^4339 ≤ 250215425244637^4339*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20073127713344489751 20000000000000000000 250215425244637 250000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250215425244637/250000000000000 : ℝ)) (X := (20073127713344489751/20000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12591408855580506799/12500000000000000000 : ℝ) ≤ (10017233871155843/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (12591408855580506799/12500000000000000000 : ℝ)^1024 ≤ (10017233871155843/10000000000000000 : ℝ)^4339 := by
      have hnat : (12591408855580506799 : ℕ)^1024*10000000000000000^4339 ≤ 10017233871155843^4339*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12591408855580506799 12500000000000000000 10017233871155843 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017233871155843/10000000000000000 : ℝ)) (X := (12591408855580506799/12500000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3144400421559/100000000000000000000 : ℝ) ≤ ((31126346912795225309/31130000000000000000 : ℝ)+2*(8616861370363/2490400000000000 : ℝ)*(53/3125 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (31126346912795225309/31130000000000000000 : ℝ)+2*(8616861370363/2490400000000000 : ℝ)*(53/3125 : ℝ)=(10000000148415117/10000000000000000 : ℝ) by norm_num, show 1+2*(3144400421559/100000000000000000000 : ℝ)=(50000003144400421559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(91408855580506799/25000000000000000000 : ℝ)+(3144400421559/100000000000000000000 : ℝ) ≤ ((31126346912795225309/31130000000000000000 : ℝ)+(8616861370363/2490400000000000 : ℝ)*((133/500 : ℝ)+(53/3125 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (31126346912795225309/31130000000000000000 : ℝ)+(8616861370363/2490400000000000 : ℝ)*((133/500 : ℝ)+(53/3125 : ℝ))=(250215425244637/250000000000000 : ℝ) by norm_num, show 1+(91408855580506799/25000000000000000000 : ℝ)+(3144400421559/100000000000000000000 : ℝ)=(20073127713344489751/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(91408855580506799/25000000000000000000 : ℝ) ≤ ((31126346912795225309/31130000000000000000 : ℝ)+2*(8616861370363/2490400000000000 : ℝ)*(133/500 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (31126346912795225309/31130000000000000000 : ℝ)+2*(8616861370363/2490400000000000 : ℝ)*(133/500 : ℝ)=(10017233871155843/10000000000000000 : ℝ) by norm_num, show 1+2*(91408855580506799/25000000000000000000 : ℝ)=(12591408855580506799/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31126346912795225309/31130000000000000000 : ℝ)*(X 1 0+X 2 0)+(8616861370363/2490400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (53/3125 : ℝ)) (hi := (133/500 : ℝ)) (c := (31126346912795225309/31130000000000000000 : ℝ)) (alpha := (8616861370363/2490400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31126346912795225309/31130000000000000000 : ℝ)*(X 0 1+X 2 1)+(8616861370363/2490400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (53/3125 : ℝ)) (hi := (133/500 : ℝ)) (c := (31126346912795225309/31130000000000000000 : ℝ)) (alpha := (8616861370363/2490400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31126346912795225309/31130000000000000000 : ℝ)*(X 0 2+X 1 2)+(8616861370363/2490400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (53/3125 : ℝ)) (hi := (133/500 : ℝ)) (c := (31126346912795225309/31130000000000000000 : ℝ)) (alpha := (8616861370363/2490400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1966241681/10000000000 : ℝ)*X 0 0+(5625492587/10000000000 : ℝ)*X 0 1+(5060166907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1350445713/2500000000 : ℝ)*X 1 0+(-2266956761/10000000000 : ℝ)*X 1 1+(2530084167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1350445881/2500000000 : ℝ)*X 2 0+(5060167093/10000000000 : ℝ)*X 2 1+(-2266957473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((214275193/500000000 : ℝ)*X 0 0+(744665993/2000000000 : ℝ)*X 0 1+(1231098029/2500000000 : ℝ)*X 0 2+(214275193/500000000 : ℝ)*X 1 0+(744665993/2000000000 : ℝ)*X 1 1+(1231098029/2500000000 : ℝ)*X 1 2+(214275193/500000000 : ℝ)*X 2 0+(744665993/2000000000 : ℝ)*X 2 1+(1231098029/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966712773/10000000000 : ℝ)*X 0 0+(5067055383/10000000000 : ℝ)*X 0 1+(1404620621/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254633601/10000000000 : ℝ)*X 1 0+(-854321191/5000000000 : ℝ)*X 1 1+(5618482571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254633913/10000000000 : ℝ)*X 2 0+(1404620717/2500000000 : ℝ)*X 2 1+(-1708641511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4286506209/10000000000 : ℝ)*X 0 0+(76714973/156250000 : ℝ)*X 0 1+(467277501/1250000000 : ℝ)*X 0 2+(4286506209/10000000000 : ℝ)*X 1 0+(76714973/156250000 : ℝ)*X 1 1+(467277501/1250000000 : ℝ)*X 1 2+(4286506209/10000000000 : ℝ)*X 2 0+(76714973/156250000 : ℝ)*X 2 1+(467277501/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54221787841292245476838179/7782500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276125429/25000000000000 : ℝ)*(base19) + (1350205803/100000000000000 : ℝ)*(base23) + (8442501/50000000000000 : ℝ)*(upper2) + (102097109/50000000000000 : ℝ)*(upper3) + (6503797911341/500000000000 : ℝ)*(major0) + (6503797911341/500000000000 : ℝ)*(major1) + (6503797911341/500000000000 : ℝ)*(major2) + (1768904325347101/100000000000000 : ℝ)*(sp0) + (442228464259501/25000000000000 : ℝ)*(sp1) + (884456702643083/50000000000000 : ℝ)*(sp2) + (832599515492391/100000000000000 : ℝ)*(sp3) + (10636192619/100000000000000 : ℝ)*(sp4) + (206047751/100000000000000 : ℝ)*(sp6) + (4455266197/100000000000000 : ℝ)*(sp7) + (208150992689647/25000000000000 : ℝ)*(f.failure) + (44222874038493/2500000000000 : ℝ)*(f.sum) + (279181632927/311300000000000000000000000 : ℝ)*base65 + (46332140852521869/15565000000000000000000000000000 : ℝ)*base67 + (69193314419841869/15565000000000000000000000000000 : ℝ)*base69 + (63295382500951869/15565000000000000000000000000000 : ℝ)*base71 + (42301020937/31130000000000000000000000 : ℝ)*base74 + (25530483304696869/15565000000000000000000000000000 : ℝ)*base75 + (116428047215916869/15565000000000000000000000000000 : ℝ)*base77 + (33592080300291869/15565000000000000000000000000000 : ℝ)*base79 + (3897345961437/1556500000000000000000000000 : ℝ)*base82 + (2448121/1250000000000000000000 : ℝ)*base89 + (2448121/1250000000000000000000 : ℝ)*base91 + (2448121/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12795891991990243889845137/8843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57835519/50000000000000 : ℝ)*(base1) + (9566379/1562500000000 : ℝ)*(base19) + (31704669/4000000000000 : ℝ)*(base23) + (26892473/50000000000000 : ℝ)*(upper3) + (9712287/10000000000000 : ℝ)*(upper5) + (166691000164459/12500000000000 : ℝ)*(major0) + (166691000164459/12500000000000 : ℝ)*(major1) + (166691000164459/12500000000000 : ℝ)*(major2) + (591997717/20000000000000 : ℝ)*(sp1) + (5555744717/100000000000000 : ℝ)*(sp2) + (906738671287481/50000000000000 : ℝ)*(sp4) + (906736827333541/50000000000000 : ℝ)*(sp5) + (906735439271241/50000000000000 : ℝ)*(sp6) + (53348663239179/6250000000000 : ℝ)*(sp7) + (853578727497901/100000000000000 : ℝ)*(f.failure) + (453369306725981/25000000000000 : ℝ)*(f.sum) + (9758085221867/15565000000000000000000000000 : ℝ)*base65 + (254760450529055331/389125000000000000000000000000000 : ℝ)*base67 + (995000509278194669/389125000000000000000000000000000 : ℝ)*base70 + (3755085426765055331/389125000000000000000000000000000 : ℝ)*base71 + (4815478660841/7782500000000000000000000000 : ℝ)*base73 + (3523157258565305331/389125000000000000000000000000000 : ℝ)*base75 + (1554790538248055331/389125000000000000000000000000000 : ℝ)*base77 + (3478242528398680331/389125000000000000000000000000000 : ℝ)*base79 + (1382504066421/1945625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (28666357/5000000000000000000000 : ℝ)*base90 + (28666357/5000000000000000000000 : ℝ)*base92 + (28666357/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1380_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (133/500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (53/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19183/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1380_s2_0 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003195583/10000000000 : ℝ)*x 0 + (5469783851/10000000000 : ℝ)*x 1 + (1298038397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003195583/10000000000 : ℝ)^1085 ≤ (12192464015917/100000000000000 : ℝ)^829 := by
    have hnat : (2003195583 : ℕ)^1085*100000000000000^829 ≤ 12192464015917^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003195583 10000000000 12192464015917 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469783851/10000000000 : ℝ)^1085 ≤ (22699894496539/50000000000000 : ℝ)^829 := by
    have hnat : (5469783851 : ℕ)^1085*50000000000000^829 ≤ 22699894496539^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469783851 10000000000 22699894496539 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298038397/2500000000 : ℝ)^1085 ≤ (21203873490819/50000000000000 : ℝ)^829 := by
    have hnat : (1298038397 : ℕ)^1085*50000000000000^829 ≤ 21203873490819^829*2500000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298038397 2500000000 21203873490819 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003195583/10000000000 : ℝ), (5469783851/10000000000 : ℝ), (1298038397/2500000000 : ℝ)] ![(12192464015917/100000000000000 : ℝ), (22699894496539/50000000000000 : ℝ), (21203873490819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003195583/10000000000 : ℝ)|^1085 ≤ (12192464015917/100000000000000 : ℝ)^829
        have hw : |(-2003195583/10000000000 : ℝ)|=(2003195583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469783851/10000000000 : ℝ)|^1085 ≤ (22699894496539/50000000000000 : ℝ)^829
        have hw : |(5469783851/10000000000 : ℝ)|=(5469783851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298038397/2500000000 : ℝ)|^1085 ≤ (21203873490819/50000000000000 : ℝ)^829
        have hw : |(1298038397/2500000000 : ℝ)|=(1298038397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s2_1 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5363336661/10000000000 : ℝ)*x 0 + (-2146363739/10000000000 : ℝ)*x 1 + (5192153583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363336661/10000000000 : ℝ)^1085 ≤ (44246919315507/100000000000000 : ℝ)^829 := by
    have hnat : (5363336661 : ℕ)^1085*100000000000000^829 ≤ 44246919315507^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363336661 10000000000 44246919315507 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146363739/10000000000 : ℝ)^1085 ≤ (3336333436009/25000000000000 : ℝ)^829 := by
    have hnat : (2146363739 : ℕ)^1085*25000000000000^829 ≤ 3336333436009^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146363739 10000000000 3336333436009 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192153583/10000000000 : ℝ)^1085 ≤ (10601936732047/25000000000000 : ℝ)^829 := by
    have hnat : (5192153583 : ℕ)^1085*25000000000000^829 ≤ 10601936732047^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192153583 10000000000 10601936732047 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363336661/10000000000 : ℝ), (-2146363739/10000000000 : ℝ), (5192153583/10000000000 : ℝ)] ![(44246919315507/100000000000000 : ℝ), (3336333436009/25000000000000 : ℝ), (10601936732047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363336661/10000000000 : ℝ)|^1085 ≤ (44246919315507/100000000000000 : ℝ)^829
        have hw : |(5363336661/10000000000 : ℝ)|=(5363336661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146363739/10000000000 : ℝ)|^1085 ≤ (3336333436009/25000000000000 : ℝ)^829
        have hw : |(-2146363739/10000000000 : ℝ)|=(2146363739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192153583/10000000000 : ℝ)|^1085 ≤ (10601936732047/25000000000000 : ℝ)^829
        have hw : |(5192153583/10000000000 : ℝ)|=(5192153583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s2_2 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5363336559/10000000000 : ℝ)*x 0 + (5192153677/10000000000 : ℝ)*x 1 + (-1717091/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363336559/10000000000 : ℝ)^1085 ≤ (22123459107081/50000000000000 : ℝ)^829 := by
    have hnat : (5363336559 : ℕ)^1085*50000000000000^829 ≤ 22123459107081^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363336559 10000000000 22123459107081 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192153677/10000000000 : ℝ)^1085 ≤ (42407747933037/100000000000000 : ℝ)^829 := by
    have hnat : (5192153677 : ℕ)^1085*100000000000000^829 ≤ 42407747933037^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192153677 10000000000 42407747933037 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1717091/8000000 : ℝ)^1085 ≤ (13345333833551/100000000000000 : ℝ)^829 := by
    have hnat : (1717091 : ℕ)^1085*100000000000000^829 ≤ 13345333833551^829*8000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717091 8000000 13345333833551 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363336559/10000000000 : ℝ), (5192153677/10000000000 : ℝ), (-1717091/8000000 : ℝ)] ![(22123459107081/50000000000000 : ℝ), (42407747933037/100000000000000 : ℝ), (13345333833551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363336559/10000000000 : ℝ)|^1085 ≤ (22123459107081/50000000000000 : ℝ)^829
        have hw : |(5363336559/10000000000 : ℝ)|=(5363336559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192153677/10000000000 : ℝ)|^1085 ≤ (42407747933037/100000000000000 : ℝ)^829
        have hw : |(5192153677/10000000000 : ℝ)|=(5192153677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1717091/8000000 : ℝ)|^1085 ≤ (13345333833551/100000000000000 : ℝ)^829
        have hw : |(-1717091/8000000 : ℝ)|=(1717091/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s2_3 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (172458179/400000000 : ℝ)*x 0 + (4025781811/10000000000 : ℝ)*x 1 + (4615623307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172458179/400000000 : ℝ)^1085 ≤ (33250143199721/100000000000000 : ℝ)^829 := by
    have hnat : (172458179 : ℕ)^1085*100000000000000^829 ≤ 33250143199721^829*400000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172458179 400000000 33250143199721 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025781811/10000000000 : ℝ)^1085 ≤ (7599162054919/25000000000000 : ℝ)^829 := by
    have hnat : (4025781811 : ℕ)^1085*25000000000000^829 ≤ 7599162054919^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025781811 10000000000 7599162054919 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4615623307/10000000000 : ℝ)^1085 ≤ (4544151069801/12500000000000 : ℝ)^829 := by
    have hnat : (4615623307 : ℕ)^1085*12500000000000^829 ≤ 4544151069801^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4615623307 10000000000 4544151069801 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172458179/400000000 : ℝ), (4025781811/10000000000 : ℝ), (4615623307/10000000000 : ℝ)] ![(33250143199721/100000000000000 : ℝ), (7599162054919/25000000000000 : ℝ), (4544151069801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172458179/400000000 : ℝ)|^1085 ≤ (33250143199721/100000000000000 : ℝ)^829
        have hw : |(172458179/400000000 : ℝ)|=(172458179/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025781811/10000000000 : ℝ)|^1085 ≤ (7599162054919/25000000000000 : ℝ)^829
        have hw : |(4025781811/10000000000 : ℝ)|=(4025781811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4615623307/10000000000 : ℝ)|^1085 ≤ (4544151069801/12500000000000 : ℝ)^829
        have hw : |(4615623307/10000000000 : ℝ)|=(4615623307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s2_4 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003251191/10000000000 : ℝ)*x 0 + (207752987/400000000 : ℝ)*x 1 + (546809849/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003251191/10000000000 : ℝ)^1085 ≤ (6096453497119/50000000000000 : ℝ)^829 := by
    have hnat : (2003251191 : ℕ)^1085*50000000000000^829 ≤ 6096453497119^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003251191 10000000000 6096453497119 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207752987/400000000 : ℝ)^1085 ≤ (5303201448841/12500000000000 : ℝ)^829 := by
    have hnat : (207752987 : ℕ)^1085*12500000000000^829 ≤ 5303201448841^829*400000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207752987 400000000 5303201448841 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546809849/1000000000 : ℝ)^1085 ≤ (11345370351023/25000000000000 : ℝ)^829 := by
    have hnat : (546809849 : ℕ)^1085*25000000000000^829 ≤ 11345370351023^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546809849 1000000000 11345370351023 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003251191/10000000000 : ℝ), (207752987/400000000 : ℝ), (546809849/1000000000 : ℝ)] ![(6096453497119/50000000000000 : ℝ), (5303201448841/12500000000000 : ℝ), (11345370351023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003251191/10000000000 : ℝ)|^1085 ≤ (6096453497119/50000000000000 : ℝ)^829
        have hw : |(-2003251191/10000000000 : ℝ)|=(2003251191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207752987/400000000 : ℝ)|^1085 ≤ (5303201448841/12500000000000 : ℝ)^829
        have hw : |(207752987/400000000 : ℝ)|=(207752987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546809849/1000000000 : ℝ)|^1085 ≤ (11345370351023/25000000000000 : ℝ)^829
        have hw : |(546809849/1000000000 : ℝ)|=(546809849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s2_5 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5291490057/10000000000 : ℝ)*x 0 + (-1870419447/10000000000 : ℝ)*x 1 + (5468098183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291490057/10000000000 : ℝ)^1085 ≤ (21736382597647/50000000000000 : ℝ)^829 := by
    have hnat : (5291490057 : ℕ)^1085*50000000000000^829 ≤ 21736382597647^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291490057 10000000000 21736382597647 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870419447/10000000000 : ℝ)^1085 ≤ (11145756728953/100000000000000 : ℝ)^829 := by
    have hnat : (1870419447 : ℕ)^1085*100000000000000^829 ≤ 11145756728953^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870419447 10000000000 11145756728953 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468098183/10000000000 : ℝ)^1085 ≤ (45381478069399/100000000000000 : ℝ)^829 := by
    have hnat : (5468098183 : ℕ)^1085*100000000000000^829 ≤ 45381478069399^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468098183 10000000000 45381478069399 100000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291490057/10000000000 : ℝ), (-1870419447/10000000000 : ℝ), (5468098183/10000000000 : ℝ)] ![(21736382597647/50000000000000 : ℝ), (11145756728953/100000000000000 : ℝ), (45381478069399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291490057/10000000000 : ℝ)|^1085 ≤ (21736382597647/50000000000000 : ℝ)^829
        have hw : |(5291490057/10000000000 : ℝ)|=(5291490057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870419447/10000000000 : ℝ)|^1085 ≤ (11145756728953/100000000000000 : ℝ)^829
        have hw : |(-1870419447/10000000000 : ℝ)|=(1870419447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468098183/10000000000 : ℝ)|^1085 ≤ (45381478069399/100000000000000 : ℝ)^829
        have hw : |(5468098183/10000000000 : ℝ)|=(5468098183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s2_6 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2645745769/5000000000 : ℝ)*x 0 + (1093619653/2000000000 : ℝ)*x 1 + (-187041729/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645745769/5000000000 : ℝ)^1085 ≤ (10868195279983/25000000000000 : ℝ)^829 := by
    have hnat : (2645745769 : ℕ)^1085*25000000000000^829 ≤ 10868195279983^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645745769 5000000000 10868195279983 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093619653/2000000000 : ℝ)^1085 ≤ (22690739480049/50000000000000 : ℝ)^829 := by
    have hnat : (1093619653 : ℕ)^1085*50000000000000^829 ≤ 22690739480049^829*2000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093619653 2000000000 22690739480049 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187041729/1000000000 : ℝ)^1085 ≤ (1393217488281/12500000000000 : ℝ)^829 := by
    have hnat : (187041729 : ℕ)^1085*12500000000000^829 ≤ 1393217488281^829*1000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187041729 1000000000 1393217488281 12500000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645745769/5000000000 : ℝ), (1093619653/2000000000 : ℝ), (-187041729/1000000000 : ℝ)] ![(10868195279983/25000000000000 : ℝ), (22690739480049/50000000000000 : ℝ), (1393217488281/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645745769/5000000000 : ℝ)|^1085 ≤ (10868195279983/25000000000000 : ℝ)^829
        have hw : |(2645745769/5000000000 : ℝ)|=(2645745769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093619653/2000000000 : ℝ)|^1085 ≤ (22690739480049/50000000000000 : ℝ)^829
        have hw : |(1093619653/2000000000 : ℝ)|=(1093619653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187041729/1000000000 : ℝ)|^1085 ≤ (1393217488281/12500000000000 : ℝ)^829
        have hw : |(-187041729/1000000000 : ℝ)|=(187041729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1380_s2_7 (p : ℝ) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4311574243/10000000000 : ℝ)*x 0 + (2306036817/5000000000 : ℝ)*x 1 + (4029361307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311574243/10000000000 : ℝ)^1085 ≤ (16625676045971/50000000000000 : ℝ)^829 := by
    have hnat : (4311574243 : ℕ)^1085*50000000000000^829 ≤ 16625676045971^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311574243 10000000000 16625676045971 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306036817/5000000000 : ℝ)^1085 ≤ (9079155440939/25000000000000 : ℝ)^829 := by
    have hnat : (2306036817 : ℕ)^1085*25000000000000^829 ≤ 9079155440939^829*5000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306036817 5000000000 9079155440939 25000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029361307/10000000000 : ℝ)^1085 ≤ (15216013064299/50000000000000 : ℝ)^829 := by
    have hnat : (4029361307 : ℕ)^1085*50000000000000^829 ≤ 15216013064299^829*10000000000^1085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029361307 10000000000 15216013064299 50000000000000 1085 829 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1085/256 : ℝ)) 1085 829 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311574243/10000000000 : ℝ), (2306036817/5000000000 : ℝ), (4029361307/10000000000 : ℝ)] ![(16625676045971/50000000000000 : ℝ), (9079155440939/25000000000000 : ℝ), (15216013064299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311574243/10000000000 : ℝ)|^1085 ≤ (16625676045971/50000000000000 : ℝ)^829
        have hw : |(4311574243/10000000000 : ℝ)|=(4311574243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2306036817/5000000000 : ℝ)|^1085 ≤ (9079155440939/25000000000000 : ℝ)^829
        have hw : |(2306036817/5000000000 : ℝ)|=(2306036817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029361307/10000000000 : ℝ)|^1085 ≤ (15216013064299/50000000000000 : ℝ)^829
        have hw : |(4029361307/10000000000 : ℝ)|=(4029361307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1380_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19183/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1009/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15961/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19183/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19183/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19183/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19183/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19183/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19183/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3617/50000 : ℝ) ^ (4339/1024 : ℝ) ≤ (734191233338339/50000000000000000000 : ℝ) := by
    have hpowers : (3617/50000 : ℝ)^4339 ≤ (734191233338339/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3617 : ℕ)^4339*50000000000000000000^1024 ≤ 734191233338339^1024*50000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3617 50000 734191233338339 50000000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3617/50000 : ℝ)) (X := (734191233338339/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19183/100000 : ℝ) ^ (4339/1024 : ℝ) ≤ (228790952486579/250000000000000000 : ℝ) := by
    have hpowers : (19183/100000 : ℝ)^4339 ≤ (228790952486579/250000000000000000 : ℝ)^1024 := by
      have hnat : (19183 : ℕ)^4339*250000000000000000^1024 ≤ 228790952486579^1024*100000^4339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19183 100000 228790952486579 250000000000000000 4339 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19183/100000 : ℝ)) (X := (228790952486579/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000734191233338339/25000000000000000000 : ℝ) ≤ (10000069306604187/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (25000734191233338339/25000000000000000000 : ℝ)^1024 ≤ (10000069306604187/10000000000000000 : ℝ)^4339 := by
      have hnat : (25000734191233338339 : ℕ)^1024*10000000000000000^4339 ≤ 10000069306604187^4339*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000734191233338339 25000000000000000000 10000069306604187 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000069306604187/10000000000000000 : ℝ)) (X := (25000734191233338339/25000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50046492381730654139/50000000000000000000 : ℝ) ≤ (5001096826402257/5000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (50046492381730654139/50000000000000000000 : ℝ)^1024 ≤ (5001096826402257/5000000000000000 : ℝ)^4339 := by
      have hnat : (50046492381730654139 : ℕ)^1024*5000000000000000^4339 ≤ 5001096826402257^4339*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046492381730654139 50000000000000000000 5001096826402257 5000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001096826402257/5000000000000000 : ℝ)) (X := (50046492381730654139/50000000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (125228790952486579/125000000000000000 : ℝ) ≤ (10004317999004841/10000000000000000 : ℝ) ^ (4339/1024 : ℝ) := by
    have hpowers : (125228790952486579/125000000000000000 : ℝ)^1024 ≤ (10004317999004841/10000000000000000 : ℝ)^4339 := by
      have hnat : (125228790952486579 : ℕ)^1024*10000000000000000^4339 ≤ 10004317999004841^4339*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125228790952486579 125000000000000000 10004317999004841 10000000000000000 1024 4339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004317999004841/10000000000000000 : ℝ)) (X := (125228790952486579/125000000000000000 : ℝ)) (by norm_num) 4339 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(734191233338339/50000000000000000000 : ℝ) ≤ ((39820031034595699809/39830000000000000000 : ℝ)+2*(708115400109/398300000000000 : ℝ)*(3617/50000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (39820031034595699809/39830000000000000000 : ℝ)+2*(708115400109/398300000000000 : ℝ)*(3617/50000 : ℝ)=(10000069306604187/10000000000000000 : ℝ) by norm_num, show 1+2*(734191233338339/50000000000000000000 : ℝ)=(25000734191233338339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(228790952486579/250000000000000000 : ℝ)+(734191233338339/50000000000000000000 : ℝ) ≤ ((39820031034595699809/39830000000000000000 : ℝ)+(708115400109/398300000000000 : ℝ)*((19183/100000 : ℝ)+(3617/50000 : ℝ)))^(4339/1024 : ℝ) := by
    rw [show (39820031034595699809/39830000000000000000 : ℝ)+(708115400109/398300000000000 : ℝ)*((19183/100000 : ℝ)+(3617/50000 : ℝ))=(5001096826402257/5000000000000000 : ℝ) by norm_num, show 1+(228790952486579/250000000000000000 : ℝ)+(734191233338339/50000000000000000000 : ℝ)=(50046492381730654139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(228790952486579/250000000000000000 : ℝ) ≤ ((39820031034595699809/39830000000000000000 : ℝ)+2*(708115400109/398300000000000 : ℝ)*(19183/100000 : ℝ))^(4339/1024 : ℝ) := by
    rw [show (39820031034595699809/39830000000000000000 : ℝ)+2*(708115400109/398300000000000 : ℝ)*(19183/100000 : ℝ)=(10004317999004841/10000000000000000 : ℝ) by norm_num, show 1+2*(228790952486579/250000000000000000 : ℝ)=(125228790952486579/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39820031034595699809/39830000000000000000 : ℝ)*(X 1 0+X 2 0)+(708115400109/398300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (3617/50000 : ℝ)) (hi := (19183/100000 : ℝ)) (c := (39820031034595699809/39830000000000000000 : ℝ)) (alpha := (708115400109/398300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39820031034595699809/39830000000000000000 : ℝ)*(X 0 1+X 2 1)+(708115400109/398300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (3617/50000 : ℝ)) (hi := (19183/100000 : ℝ)) (c := (39820031034595699809/39830000000000000000 : ℝ)) (alpha := (708115400109/398300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39820031034595699809/39830000000000000000 : ℝ)*(X 0 2+X 1 2)+(708115400109/398300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4339/1024 : ℝ)) (lo := (3617/50000 : ℝ)) (hi := (19183/100000 : ℝ)) (c := (39820031034595699809/39830000000000000000 : ℝ)) (alpha := (708115400109/398300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2003195583/10000000000 : ℝ)*X 0 0+(5469783851/10000000000 : ℝ)*X 0 1+(1298038397/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363336661/10000000000 : ℝ)*X 1 0+(-2146363739/10000000000 : ℝ)*X 1 1+(5192153583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5363336559/10000000000 : ℝ)*X 2 0+(5192153677/10000000000 : ℝ)*X 2 1+(-1717091/8000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172458179/400000000 : ℝ)*X 0 0+(4025781811/10000000000 : ℝ)*X 0 1+(4615623307/10000000000 : ℝ)*X 0 2+(172458179/400000000 : ℝ)*X 1 0+(4025781811/10000000000 : ℝ)*X 1 1+(4615623307/10000000000 : ℝ)*X 1 2+(172458179/400000000 : ℝ)*X 2 0+(4025781811/10000000000 : ℝ)*X 2 1+(4615623307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2003251191/10000000000 : ℝ)*X 0 0+(207752987/400000000 : ℝ)*X 0 1+(546809849/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291490057/10000000000 : ℝ)*X 1 0+(-1870419447/10000000000 : ℝ)*X 1 1+(5468098183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645745769/5000000000 : ℝ)*X 2 0+(1093619653/2000000000 : ℝ)*X 2 1+(-187041729/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311574243/10000000000 : ℝ)*X 0 0+(2306036817/5000000000 : ℝ)*X 0 1+(4029361307/10000000000 : ℝ)*X 0 2+(4311574243/10000000000 : ℝ)*X 1 0+(2306036817/5000000000 : ℝ)*X 1 1+(4029361307/10000000000 : ℝ)*X 1 2+(4311574243/10000000000 : ℝ)*X 2 0+(2306036817/5000000000 : ℝ)*X 2 1+(4029361307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1380_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3729110574506409890730029151/497875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1340643713/100000000000000 : ℝ)*(base19) + (1159286131/100000000000000 : ℝ)*(base23) + (60528343/100000000000000 : ℝ)*(lower2) + (4312571/2000000000000 : ℝ)*(upper3) + (20396553/20000000000000 : ℝ)*(upper5) + (662166534420271/25000000000000 : ℝ)*(major0) + (662166534420271/25000000000000 : ℝ)*(major1) + (662166534420271/25000000000000 : ℝ)*(major2) + (72038605427431/2000000000000 : ℝ)*(sp0) + (144077776383707/4000000000000 : ℝ)*(sp1) + (3601944590950257/100000000000000 : ℝ)*(sp2) + (423844461372429/25000000000000 : ℝ)*(sp3) + (15478864839/100000000000000 : ℝ)*(sp4) + (842996759/10000000000000 : ℝ)*(sp7) + (339077255091461/20000000000000 : ℝ)*(f.failure) + (900486437559097/25000000000000 : ℝ)*(f.sum) + (12843999676691/19915000000000000000000000000 : ℝ)*base65 + (17824001447463921761/995750000000000000000000000000000 : ℝ)*base68 + (20351758966514671761/995750000000000000000000000000000 : ℝ)*base70 + (12899024470694421761/995750000000000000000000000000000 : ℝ)*base72 + (34494738779409/19915000000000000000000000000 : ℝ)*base74 + (17372664173950921761/995750000000000000000000000000000 : ℝ)*base76 + (2955452511870421761/995750000000000000000000000000000 : ℝ)*base78 + (22013822321104421761/995750000000000000000000000000000 : ℝ)*base80 + (17269788322631/4978750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4340723/1000000000000000000000 : ℝ)*base89 + (4340723/1000000000000000000000 : ℝ)*base91 + (4340723/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4671052439887307979648875877/1991500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (635777503/100000000000000 : ℝ)*(base19) + (2357749207/100000000000000 : ℝ)*(base23) + (100695953/100000000000000 : ℝ)*(lower2) + (176196139/100000000000000 : ℝ)*(upper3) + (102278303/50000000000000 : ℝ)*(lower4) + (2681055836851351/100000000000000 : ℝ)*(major0) + (2681055836851351/100000000000000 : ℝ)*(major1) + (2681055836851351/100000000000000 : ℝ)*(major2) + (18605864929/50000000000000 : ℝ)*(sp2) + (381257383/50000000000000 : ℝ)*(sp3) + (3645992978353239/100000000000000 : ℝ)*(sp4) + (455749042821967/12500000000000 : ℝ)*(sp5) + (1822976704437087/50000000000000 : ℝ)*(sp6) + (858058927325769/50000000000000 : ℝ)*(sp7) + (343223723433261/20000000000000 : ℝ)*(f.failure) + (3645992978353239/100000000000000 : ℝ)*(f.sum) + (42794549875867/9957500000000000000000000000 : ℝ)*base65 + (1017571708391008041/3983000000000000000000000000000000 : ℝ)*base68 + (696772105876008041/3983000000000000000000000000000000 : ℝ)*base70 + (13480091506210008041/3983000000000000000000000000000000 : ℝ)*base72 + (91476443924969/19915000000000000000000000000 : ℝ)*base73 + (52281196217949991959/3983000000000000000000000000000000 : ℝ)*base75 + (21675358092416008041/3983000000000000000000000000000000 : ℝ)*base78 + (28401966989675991959/3983000000000000000000000000000000 : ℝ)*base79 + (71277793743539/19915000000000000000000000000 : ℝ)*base81 + (4058123/1000000000000000000000 : ℝ)*base89 + (4058123/1000000000000000000000 : ℝ)*base91 + (4058123/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1380_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19183/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1380_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1380_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1380_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1380_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1380_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4339/1024 : ℝ) ≤ p) (hpb : p ≤ (1085/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78113943/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1009/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15961/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1380_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
