-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:33.866653+00:00
-- url     : https://prove2.me/submissions/742f8a45-818d-4c35-a35b-5a9890c7d3cb

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
theorem support_rectangle_w1172_s3_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149134349/10000000000 : ℝ)*x 0 + (1356540001/2500000000 : ℝ)*x 1 + (2617412411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149134349/10000000000 : ℝ)^8365 ≤ (2611021126561/20000000000000 : ℝ)^6317 := by
    have hnat : (2149134349 : ℕ)^8365*20000000000000^6317 ≤ 2611021126561^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149134349 10000000000 2611021126561 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356540001/2500000000 : ℝ)^8365 ≤ (22252760702797/50000000000000 : ℝ)^6317 := by
    have hnat : (1356540001 : ℕ)^8365*50000000000000^6317 ≤ 22252760702797^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356540001 2500000000 22252760702797 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617412411/5000000000 : ℝ)^8365 ≤ (10609843235217/25000000000000 : ℝ)^6317 := by
    have hnat : (2617412411 : ℕ)^8365*25000000000000^6317 ≤ 10609843235217^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617412411 5000000000 10609843235217 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149134349/10000000000 : ℝ), (1356540001/2500000000 : ℝ), (2617412411/5000000000 : ℝ)] ![(2611021126561/20000000000000 : ℝ), (22252760702797/50000000000000 : ℝ), (10609843235217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149134349/10000000000 : ℝ)|^8365 ≤ (2611021126561/20000000000000 : ℝ)^6317
        have hw : |(-2149134349/10000000000 : ℝ)|=(2149134349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356540001/2500000000 : ℝ)|^8365 ≤ (22252760702797/50000000000000 : ℝ)^6317
        have hw : |(1356540001/2500000000 : ℝ)|=(1356540001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617412411/5000000000 : ℝ)|^8365 ≤ (10609843235217/25000000000000 : ℝ)^6317
        have hw : |(2617412411/5000000000 : ℝ)|=(2617412411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s3_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338270657/2500000000 : ℝ)*x 0 + (-2246875729/10000000000 : ℝ)*x 1 + (41878597/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338270657/2500000000 : ℝ)^8365 ≤ (43713554098279/100000000000000 : ℝ)^6317 := by
    have hnat : (1338270657 : ℕ)^8365*100000000000000^6317 ≤ 43713554098279^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338270657 2500000000 43713554098279 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246875729/10000000000 : ℝ)^8365 ≤ (13847075056029/100000000000000 : ℝ)^6317 := by
    have hnat : (2246875729 : ℕ)^8365*100000000000000^6317 ≤ 13847075056029^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246875729 10000000000 13847075056029 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41878597/80000000 : ℝ)^8365 ≤ (5304921353247/12500000000000 : ℝ)^6317 := by
    have hnat : (41878597 : ℕ)^8365*12500000000000^6317 ≤ 5304921353247^6317*80000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41878597 80000000 5304921353247 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338270657/2500000000 : ℝ), (-2246875729/10000000000 : ℝ), (41878597/80000000 : ℝ)] ![(43713554098279/100000000000000 : ℝ), (13847075056029/100000000000000 : ℝ), (5304921353247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338270657/2500000000 : ℝ)|^8365 ≤ (43713554098279/100000000000000 : ℝ)^6317
        have hw : |(1338270657/2500000000 : ℝ)|=(1338270657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246875729/10000000000 : ℝ)|^8365 ≤ (13847075056029/100000000000000 : ℝ)^6317
        have hw : |(-2246875729/10000000000 : ℝ)|=(2246875729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41878597/80000000 : ℝ)|^8365 ≤ (5304921353247/12500000000000 : ℝ)^6317
        have hw : |(41878597/80000000 : ℝ)|=(41878597/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s3_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353082713/10000000000 : ℝ)*x 0 + (2617412309/5000000000 : ℝ)*x 1 + (-1123437813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353082713/10000000000 : ℝ)^8365 ≤ (10928388754357/25000000000000 : ℝ)^6317 := by
    have hnat : (5353082713 : ℕ)^8365*25000000000000^6317 ≤ 10928388754357^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353082713 10000000000 10928388754357 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617412309/5000000000 : ℝ)^8365 ≤ (10609842687707/25000000000000 : ℝ)^6317 := by
    have hnat : (2617412309 : ℕ)^8365*25000000000000^6317 ≤ 10609842687707^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617412309 5000000000 10609842687707 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123437813/5000000000 : ℝ)^8365 ≤ (1730884276933/12500000000000 : ℝ)^6317 := by
    have hnat : (1123437813 : ℕ)^8365*12500000000000^6317 ≤ 1730884276933^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123437813 5000000000 1730884276933 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353082713/10000000000 : ℝ), (2617412309/5000000000 : ℝ), (-1123437813/5000000000 : ℝ)] ![(10928388754357/25000000000000 : ℝ), (10609842687707/25000000000000 : ℝ), (1730884276933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353082713/10000000000 : ℝ)|^8365 ≤ (10928388754357/25000000000000 : ℝ)^6317
        have hw : |(5353082713/10000000000 : ℝ)|=(5353082713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617412309/5000000000 : ℝ)|^8365 ≤ (10609842687707/25000000000000 : ℝ)^6317
        have hw : |(2617412309/5000000000 : ℝ)|=(2617412309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123437813/5000000000 : ℝ)|^8365 ≤ (1730884276933/12500000000000 : ℝ)^6317
        have hw : |(-1123437813/5000000000 : ℝ)|=(1123437813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s3_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179195333/5000000000 : ℝ)*x 0 + (4171091477/10000000000 : ℝ)*x 1 + (889451/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179195333/5000000000 : ℝ)^8365 ≤ (33296153312003/100000000000000 : ℝ)^6317 := by
    have hnat : (2179195333 : ℕ)^8365*100000000000000^6317 ≤ 33296153312003^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179195333 5000000000 33296153312003 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171091477/10000000000 : ℝ)^8365 ≤ (31414702603429/100000000000000 : ℝ)^6317 := by
    have hnat : (4171091477 : ℕ)^8365*100000000000000^6317 ≤ 31414702603429^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171091477 10000000000 31414702603429 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889451/1953125 : ℝ)^8365 ≤ (8822286018391/25000000000000 : ℝ)^6317 := by
    have hnat : (889451 : ℕ)^8365*25000000000000^6317 ≤ 8822286018391^6317*1953125^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889451 1953125 8822286018391 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179195333/5000000000 : ℝ), (4171091477/10000000000 : ℝ), (889451/1953125 : ℝ)] ![(33296153312003/100000000000000 : ℝ), (31414702603429/100000000000000 : ℝ), (8822286018391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179195333/5000000000 : ℝ)|^8365 ≤ (33296153312003/100000000000000 : ℝ)^6317
        have hw : |(2179195333/5000000000 : ℝ)|=(2179195333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171091477/10000000000 : ℝ)|^8365 ≤ (31414702603429/100000000000000 : ℝ)^6317
        have hw : |(4171091477/10000000000 : ℝ)|=(4171091477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(889451/1953125 : ℝ)|^8365 ≤ (8822286018391/25000000000000 : ℝ)^6317
        have hw : |(889451/1953125 : ℝ)|=(889451/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s3_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-537287741/2500000000 : ℝ)*x 0 + (2617775973/5000000000 : ℝ)*x 1 + (1356357239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537287741/2500000000 : ℝ)^8365 ≤ (13055239283981/100000000000000 : ℝ)^6317 := by
    have hnat : (537287741 : ℕ)^8365*100000000000000^6317 ≤ 13055239283981^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537287741 2500000000 13055239283981 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617775973/5000000000 : ℝ)^8365 ≤ (10611794787273/25000000000000 : ℝ)^6317 := by
    have hnat : (2617775973 : ℕ)^8365*25000000000000^6317 ≤ 10611794787273^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617775973 5000000000 10611794787273 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356357239/2500000000 : ℝ)^8365 ≤ (44497581546887/100000000000000 : ℝ)^6317 := by
    have hnat : (1356357239 : ℕ)^8365*100000000000000^6317 ≤ 44497581546887^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356357239 2500000000 44497581546887 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537287741/2500000000 : ℝ), (2617775973/5000000000 : ℝ), (1356357239/2500000000 : ℝ)] ![(13055239283981/100000000000000 : ℝ), (10611794787273/25000000000000 : ℝ), (44497581546887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537287741/2500000000 : ℝ)|^8365 ≤ (13055239283981/100000000000000 : ℝ)^6317
        have hw : |(-537287741/2500000000 : ℝ)|=(537287741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617775973/5000000000 : ℝ)|^8365 ≤ (10611794787273/25000000000000 : ℝ)^6317
        have hw : |(2617775973/5000000000 : ℝ)|=(2617775973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356357239/2500000000 : ℝ)|^8365 ≤ (44497581546887/100000000000000 : ℝ)^6317
        have hw : |(1356357239/2500000000 : ℝ)|=(1356357239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s3_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663062911/1250000000 : ℝ)*x 0 + (-2056272071/10000000000 : ℝ)*x 1 + (5425428781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663062911/1250000000 : ℝ)^8365 ≤ (5398626826963/12500000000000 : ℝ)^6317 := by
    have hnat : (663062911 : ℕ)^8365*12500000000000^6317 ≤ 5398626826963^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663062911 1250000000 5398626826963 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056272071/10000000000 : ℝ)^8365 ≤ (3078351432459/25000000000000 : ℝ)^6317 := by
    have hnat : (2056272071 : ℕ)^8365*25000000000000^6317 ≤ 3078351432459^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056272071 10000000000 3078351432459 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425428781/10000000000 : ℝ)^8365 ≤ (44497579646267/100000000000000 : ℝ)^6317 := by
    have hnat : (5425428781 : ℕ)^8365*100000000000000^6317 ≤ 44497579646267^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425428781 10000000000 44497579646267 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663062911/1250000000 : ℝ), (-2056272071/10000000000 : ℝ), (5425428781/10000000000 : ℝ)] ![(5398626826963/12500000000000 : ℝ), (3078351432459/25000000000000 : ℝ), (44497579646267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663062911/1250000000 : ℝ)|^8365 ≤ (5398626826963/12500000000000 : ℝ)^6317
        have hw : |(663062911/1250000000 : ℝ)|=(663062911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056272071/10000000000 : ℝ)|^8365 ≤ (3078351432459/25000000000000 : ℝ)^6317
        have hw : |(-2056272071/10000000000 : ℝ)|=(2056272071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425428781/10000000000 : ℝ)|^8365 ≤ (44497579646267/100000000000000 : ℝ)^6317
        have hw : |(5425428781/10000000000 : ℝ)|=(5425428781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s3_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652252257/5000000000 : ℝ)*x 0 + (5425427677/10000000000 : ℝ)*x 1 + (-411254383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652252257/5000000000 : ℝ)^8365 ≤ (43189027833959/100000000000000 : ℝ)^6317 := by
    have hnat : (2652252257 : ℕ)^8365*100000000000000^6317 ≤ 43189027833959^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652252257 5000000000 43189027833959 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425427677/10000000000 : ℝ)^8365 ≤ (22248783828033/50000000000000 : ℝ)^6317 := by
    have hnat : (5425427677 : ℕ)^8365*50000000000000^6317 ≤ 22248783828033^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425427677 10000000000 22248783828033 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411254383/2000000000 : ℝ)^8365 ≤ (6156702246407/50000000000000 : ℝ)^6317 := by
    have hnat : (411254383 : ℕ)^8365*50000000000000^6317 ≤ 6156702246407^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411254383 2000000000 6156702246407 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652252257/5000000000 : ℝ), (5425427677/10000000000 : ℝ), (-411254383/2000000000 : ℝ)] ![(43189027833959/100000000000000 : ℝ), (22248783828033/50000000000000 : ℝ), (6156702246407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652252257/5000000000 : ℝ)|^8365 ≤ (43189027833959/100000000000000 : ℝ)^6317
        have hw : |(2652252257/5000000000 : ℝ)|=(2652252257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425427677/10000000000 : ℝ)|^8365 ≤ (22248783828033/50000000000000 : ℝ)^6317
        have hw : |(5425427677/10000000000 : ℝ)|=(5425427677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411254383/2000000000 : ℝ)|^8365 ≤ (6156702246407/50000000000000 : ℝ)^6317
        have hw : |(-411254383/2000000000 : ℝ)|=(411254383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s3_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358423629/10000000000 : ℝ)*x 0 + (2276267153/5000000000 : ℝ)*x 1 + (4172554713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358423629/10000000000 : ℝ)^8365 ≤ (8324121694247/25000000000000 : ℝ)^6317 := by
    have hnat : (4358423629 : ℕ)^8365*25000000000000^6317 ≤ 8324121694247^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358423629 10000000000 8324121694247 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276267153/5000000000 : ℝ)^8365 ≤ (17637108250619/50000000000000 : ℝ)^6317 := by
    have hnat : (2276267153 : ℕ)^8365*50000000000000^6317 ≤ 17637108250619^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276267153 5000000000 17637108250619 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172554713/10000000000 : ℝ)^8365 ≤ (31429296705457/100000000000000 : ℝ)^6317 := by
    have hnat : (4172554713 : ℕ)^8365*100000000000000^6317 ≤ 31429296705457^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172554713 10000000000 31429296705457 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358423629/10000000000 : ℝ), (2276267153/5000000000 : ℝ), (4172554713/10000000000 : ℝ)] ![(8324121694247/25000000000000 : ℝ), (17637108250619/50000000000000 : ℝ), (31429296705457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358423629/10000000000 : ℝ)|^8365 ≤ (8324121694247/25000000000000 : ℝ)^6317
        have hw : |(4358423629/10000000000 : ℝ)|=(4358423629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2276267153/5000000000 : ℝ)|^8365 ≤ (17637108250619/50000000000000 : ℝ)^6317
        have hw : |(2276267153/5000000000 : ℝ)|=(2276267153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172554713/10000000000 : ℝ)|^8365 ≤ (31429296705457/100000000000000 : ℝ)^6317
        have hw : |(4172554713/10000000000 : ℝ)|=(4172554713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5361/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3283/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2301/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3283/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2301/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3283/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2301/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3283/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2301/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3283/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2301/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3283/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2301/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2301/25000 : ℝ) ^ (2091/512 : ℝ) ≤ (1468373951882809/25000000000000000000 : ℝ) := by
    have hpowers : (2301/25000 : ℝ)^2091 ≤ (1468373951882809/25000000000000000000 : ℝ)^512 := by
      have hnat : (2301 : ℕ)^2091*25000000000000000000^512 ≤ 1468373951882809^512*25000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2301 25000 1468373951882809 25000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2301/25000 : ℝ)) (X := (1468373951882809/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3283/20000 : ℝ) ^ (2091/512 : ℝ) ≤ (3119076660622989/5000000000000000000 : ℝ) := by
    have hpowers : (3283/20000 : ℝ)^2091 ≤ (3119076660622989/5000000000000000000 : ℝ)^512 := by
      have hnat : (3283 : ℕ)^2091*5000000000000000000^512 ≤ 3119076660622989^512*20000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3283 20000 3119076660622989 5000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3283/20000 : ℝ)) (X := (3119076660622989/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501468373951882809/12500000000000000000 : ℝ) ≤ (1000028762281037/1000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (12501468373951882809/12500000000000000000 : ℝ)^512 ≤ (1000028762281037/1000000000000000 : ℝ)^2091 := by
      have hnat : (12501468373951882809 : ℕ)^512*1000000000000000^2091 ≤ 1000028762281037^2091*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501468373951882809 12500000000000000000 1000028762281037 1000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000028762281037/1000000000000000 : ℝ)) (X := (12501468373951882809/12500000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12508531878627498877/12500000000000000000 : ℝ) ≤ (10001670854726939/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (12508531878627498877/12500000000000000000 : ℝ)^512 ≤ (10001670854726939/10000000000000000 : ℝ)^2091 := by
      have hnat : (12508531878627498877 : ℕ)^512*10000000000000000^2091 ≤ 10001670854726939^2091*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508531878627498877 12500000000000000000 10001670854726939 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001670854726939/10000000000000000 : ℝ)) (X := (12508531878627498877/12500000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2503119076660622989/2500000000000000000 : ℝ) ≤ (2500763521660877/2500000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (2503119076660622989/2500000000000000000 : ℝ)^512 ≤ (2500763521660877/2500000000000000 : ℝ)^2091 := by
      have hnat : (2503119076660622989 : ℕ)^512*2500000000000000^2091 ≤ 2500763521660877^2091*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2503119076660622989 2500000000000000000 2500763521660877 2500000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500763521660877/2500000000000000 : ℝ)) (X := (2503119076660622989/2500000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1468373951882809/25000000000000000000 : ℝ) ≤ ((36043305757482687959/36055000000000000000 : ℝ)+2*(1383231916569/721100000000000 : ℝ)*(2301/25000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (36043305757482687959/36055000000000000000 : ℝ)+2*(1383231916569/721100000000000 : ℝ)*(2301/25000 : ℝ)=(1000028762281037/1000000000000000 : ℝ) by norm_num, show 1+2*(1468373951882809/25000000000000000000 : ℝ)=(12501468373951882809/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3119076660622989/5000000000000000000 : ℝ)+(1468373951882809/25000000000000000000 : ℝ) ≤ ((36043305757482687959/36055000000000000000 : ℝ)+(1383231916569/721100000000000 : ℝ)*((3283/20000 : ℝ)+(2301/25000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (36043305757482687959/36055000000000000000 : ℝ)+(1383231916569/721100000000000 : ℝ)*((3283/20000 : ℝ)+(2301/25000 : ℝ))=(10001670854726939/10000000000000000 : ℝ) by norm_num, show 1+(3119076660622989/5000000000000000000 : ℝ)+(1468373951882809/25000000000000000000 : ℝ)=(12508531878627498877/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3119076660622989/5000000000000000000 : ℝ) ≤ ((36043305757482687959/36055000000000000000 : ℝ)+2*(1383231916569/721100000000000 : ℝ)*(3283/20000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (36043305757482687959/36055000000000000000 : ℝ)+2*(1383231916569/721100000000000 : ℝ)*(3283/20000 : ℝ)=(2500763521660877/2500000000000000 : ℝ) by norm_num, show 1+2*(3119076660622989/5000000000000000000 : ℝ)=(2503119076660622989/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36043305757482687959/36055000000000000000 : ℝ)*(X 1 0+X 2 0)+(1383231916569/721100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (2301/25000 : ℝ)) (hi := (3283/20000 : ℝ)) (c := (36043305757482687959/36055000000000000000 : ℝ)) (alpha := (1383231916569/721100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36043305757482687959/36055000000000000000 : ℝ)*(X 0 1+X 2 1)+(1383231916569/721100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (2301/25000 : ℝ)) (hi := (3283/20000 : ℝ)) (c := (36043305757482687959/36055000000000000000 : ℝ)) (alpha := (1383231916569/721100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36043305757482687959/36055000000000000000 : ℝ)*(X 0 2+X 1 2)+(1383231916569/721100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (2301/25000 : ℝ)) (hi := (3283/20000 : ℝ)) (c := (36043305757482687959/36055000000000000000 : ℝ)) (alpha := (1383231916569/721100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149134349/10000000000 : ℝ)*X 0 0+(1356540001/2500000000 : ℝ)*X 0 1+(2617412411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338270657/2500000000 : ℝ)*X 1 0+(-2246875729/10000000000 : ℝ)*X 1 1+(41878597/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353082713/10000000000 : ℝ)*X 2 0+(2617412309/5000000000 : ℝ)*X 2 1+(-1123437813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179195333/5000000000 : ℝ)*X 0 0+(4171091477/10000000000 : ℝ)*X 0 1+(889451/1953125 : ℝ)*X 0 2+(2179195333/5000000000 : ℝ)*X 1 0+(4171091477/10000000000 : ℝ)*X 1 1+(889451/1953125 : ℝ)*X 1 2+(2179195333/5000000000 : ℝ)*X 2 0+(4171091477/10000000000 : ℝ)*X 2 1+(889451/1953125 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-537287741/2500000000 : ℝ)*X 0 0+(2617775973/5000000000 : ℝ)*X 0 1+(1356357239/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663062911/1250000000 : ℝ)*X 1 0+(-2056272071/10000000000 : ℝ)*X 1 1+(5425428781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652252257/5000000000 : ℝ)*X 2 0+(5425427677/10000000000 : ℝ)*X 2 1+(-411254383/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358423629/10000000000 : ℝ)*X 0 0+(2276267153/5000000000 : ℝ)*X 0 1+(4172554713/10000000000 : ℝ)*X 0 2+(4358423629/10000000000 : ℝ)*X 1 0+(2276267153/5000000000 : ℝ)*X 1 1+(4172554713/10000000000 : ℝ)*X 1 2+(4358423629/10000000000 : ℝ)*X 2 0+(2276267153/5000000000 : ℝ)*X 2 1+(4172554713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5916393356147472615892436259/901375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (317902133/20000000000000 : ℝ)*(base19) + (771037973/50000000000000 : ℝ)*(base23) + (34908639/50000000000000 : ℝ)*(lower2) + (67868589/50000000000000 : ℝ)*(upper3) + (163659323/100000000000000 : ℝ)*(upper5) + (3919086037159567/100000000000000 : ℝ)*(major0) + (3919086037159567/100000000000000 : ℝ)*(major1) + (3919086037159567/100000000000000 : ℝ)*(major2) + (81663351783469/1562500000000 : ℝ)*(sp0) + (20415938045781/390625000000 : ℝ)*(sp1) + (1045296037430931/20000000000000 : ℝ)*(sp2) + (20893414611799/800000000000 : ℝ)*(sp3) + (5443017717/20000000000000 : ℝ)*(sp4) + (13299822239/100000000000000 : ℝ)*(sp7) + (1305845063148557/50000000000000 : ℝ)*(f.failure) + (5226481729230601/100000000000000 : ℝ)*(f.sum) + (784380985747/9013750000000000000000000000 : ℝ)*base65 + (1649397759872796247/3605500000000000000000000000000000 : ℝ)*base68 + (6283874618929203753/3605500000000000000000000000000000 : ℝ)*base69 + (19218414829955796247/3605500000000000000000000000000000 : ℝ)*base72 + (13695770156637/9013750000000000000000000000 : ℝ)*base73 + (19034795793604796247/3605500000000000000000000000000000 : ℝ)*base76 + (41396231864794296247/3605500000000000000000000000000000 : ℝ)*base78 + (16118385775210796247/3605500000000000000000000000000000 : ℝ)*base80 + (6280072687993/2253437500000000000000000000 : ℝ)*base81 + (24463217/5000000000000000000000 : ℝ)*base89 + (24463217/5000000000000000000000 : ℝ)*base91 + (24463217/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1015661400810494446479601509/225343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (278661353/100000000000000 : ℝ)*(base19) + (815983143/50000000000000 : ℝ)*(base23) + (20199137/100000000000000 : ℝ)*(upper2) + (15070761/50000000000000 : ℝ)*(upper3) + (14428693/100000000000000 : ℝ)*(upper5) + (987287489651567/25000000000000 : ℝ)*(major0) + (987287489651567/25000000000000 : ℝ)*(major1) + (987287489651567/25000000000000 : ℝ)*(major2) + (135596097/50000000000000 : ℝ)*(sp1) + (10971475703/100000000000000 : ℝ)*(sp2) + (2633287478787787/50000000000000 : ℝ)*(sp4) + (5266574407722027/100000000000000 : ℝ)*(sp5) + (1053312470826717/20000000000000 : ℝ)*(sp6) + (2631724809398133/100000000000000 : ℝ)*(sp7) + (2631724809398133/100000000000000 : ℝ)*(f.failure) + (2633287478787787/50000000000000 : ℝ)*(f.sum) + (43895978675837/36055000000000000000000000000 : ℝ)*base65 + (4443973020462718247/901375000000000000000000000000000 : ℝ)*base68 + (7938472178435343247/901375000000000000000000000000000 : ℝ)*base70 + (2329074661311843247/901375000000000000000000000000000 : ℝ)*base72 + (31085875410033/36055000000000000000000000000 : ℝ)*base74 + (15559161171075718247/901375000000000000000000000000000 : ℝ)*base76 + (4288645432596781753/901375000000000000000000000000000 : ℝ)*base77 + (3875855733018343247/901375000000000000000000000000000 : ℝ)*base80 + (8286639819711/4506875000000000000000000000 : ℝ)*base82 + (20535673/10000000000000000000000 : ℝ)*base89 + (20535673/10000000000000000000000 : ℝ)*base91 + (20535673/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1172_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5361/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_s4_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-215190649/1000000000 : ℝ)*x 0 + (2700245421/5000000000 : ℝ)*x 1 + (5258679367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215190649/1000000000 : ℝ)^8365 ≤ (3269352346897/25000000000000 : ℝ)^6317 := by
    have hnat : (215190649 : ℕ)^8365*25000000000000^6317 ≤ 3269352346897^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215190649 1000000000 3269352346897 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700245421/5000000000 : ℝ)^8365 ≤ (44226938453559/100000000000000 : ℝ)^6317 := by
    have hnat : (2700245421 : ℕ)^8365*100000000000000^6317 ≤ 44226938453559^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700245421 5000000000 44226938453559 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258679367/10000000000 : ℝ)^8365 ≤ (8539130429407/20000000000000 : ℝ)^6317 := by
    have hnat : (5258679367 : ℕ)^8365*20000000000000^6317 ≤ 8539130429407^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258679367 10000000000 8539130429407 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215190649/1000000000 : ℝ), (2700245421/5000000000 : ℝ), (5258679367/10000000000 : ℝ)] ![(3269352346897/25000000000000 : ℝ), (44226938453559/100000000000000 : ℝ), (8539130429407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215190649/1000000000 : ℝ)|^8365 ≤ (3269352346897/25000000000000 : ℝ)^6317
        have hw : |(-215190649/1000000000 : ℝ)|=(215190649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700245421/5000000000 : ℝ)|^8365 ≤ (44226938453559/100000000000000 : ℝ)^6317
        have hw : |(2700245421/5000000000 : ℝ)|=(2700245421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258679367/10000000000 : ℝ)|^8365 ≤ (8539130429407/20000000000000 : ℝ)^6317
        have hw : |(5258679367/10000000000 : ℝ)|=(5258679367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s4_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534665271/1000000000 : ℝ)*x 0 + (-17374623/78125000 : ℝ)*x 1 + (5258679713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534665271/1000000000 : ℝ)^8365 ≤ (21822018784537/50000000000000 : ℝ)^6317 := by
    have hnat : (534665271 : ℕ)^8365*50000000000000^6317 ≤ 21822018784537^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534665271 1000000000 21822018784537 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17374623/78125000 : ℝ)^8365 ≤ (6830153272289/50000000000000 : ℝ)^6317 := by
    have hnat : (17374623 : ℕ)^8365*50000000000000^6317 ≤ 6830153272289^6317*78125000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17374623 78125000 6830153272289 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258679713/10000000000 : ℝ)^8365 ≤ (21347827933497/50000000000000 : ℝ)^6317 := by
    have hnat : (5258679713 : ℕ)^8365*50000000000000^6317 ≤ 21347827933497^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258679713 10000000000 21347827933497 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534665271/1000000000 : ℝ), (-17374623/78125000 : ℝ), (5258679713/10000000000 : ℝ)] ![(21822018784537/50000000000000 : ℝ), (6830153272289/50000000000000 : ℝ), (21347827933497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534665271/1000000000 : ℝ)|^8365 ≤ (21822018784537/50000000000000 : ℝ)^6317
        have hw : |(534665271/1000000000 : ℝ)|=(534665271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17374623/78125000 : ℝ)|^8365 ≤ (6830153272289/50000000000000 : ℝ)^6317
        have hw : |(-17374623/78125000 : ℝ)|=(17374623/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258679713/10000000000 : ℝ)|^8365 ≤ (21347827933497/50000000000000 : ℝ)^6317
        have hw : |(5258679713/10000000000 : ℝ)|=(5258679713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s4_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346652713/10000000000 : ℝ)*x 0 + (2629339997/5000000000 : ℝ)*x 1 + (-2223951369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346652713/10000000000 : ℝ)^8365 ≤ (21822018800751/50000000000000 : ℝ)^6317 := by
    have hnat : (5346652713 : ℕ)^8365*50000000000000^6317 ≤ 21822018800751^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346652713 10000000000 21822018800751 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629339997/5000000000 : ℝ)^8365 ≤ (42695658888117/100000000000000 : ℝ)^6317 := by
    have hnat : (2629339997 : ℕ)^8365*100000000000000^6317 ≤ 42695658888117^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629339997 5000000000 42695658888117 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223951369/10000000000 : ℝ)^8365 ≤ (13660303494427/100000000000000 : ℝ)^6317 := by
    have hnat : (2223951369 : ℕ)^8365*100000000000000^6317 ≤ 13660303494427^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223951369 10000000000 13660303494427 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346652713/10000000000 : ℝ), (2629339997/5000000000 : ℝ), (-2223951369/10000000000 : ℝ)] ![(21822018800751/50000000000000 : ℝ), (42695658888117/100000000000000 : ℝ), (13660303494427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346652713/10000000000 : ℝ)|^8365 ≤ (21822018800751/50000000000000 : ℝ)^6317
        have hw : |(5346652713/10000000000 : ℝ)|=(5346652713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629339997/5000000000 : ℝ)|^8365 ≤ (42695658888117/100000000000000 : ℝ)^6317
        have hw : |(2629339997/5000000000 : ℝ)|=(2629339997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223951369/10000000000 : ℝ)|^8365 ≤ (13660303494427/100000000000000 : ℝ)^6317
        have hw : |(-2223951369/10000000000 : ℝ)|=(2223951369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s4_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180023177/5000000000 : ℝ)*x 0 + (422043109/1000000000 : ℝ)*x 1 + (563027761/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180023177/5000000000 : ℝ)^8365 ≤ (666258076581/2000000000000 : ℝ)^6317 := by
    have hnat : (2180023177 : ℕ)^8365*2000000000000^6317 ≤ 666258076581^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180023177 5000000000 666258076581 2000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422043109/1000000000 : ℝ)^8365 ≤ (31907721769991/100000000000000 : ℝ)^6317 := by
    have hnat : (422043109 : ℕ)^8365*100000000000000^6317 ≤ 31907721769991^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422043109 1000000000 31907721769991 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563027761/1250000000 : ℝ)^8365 ≤ (2173710899027/6250000000000 : ℝ)^6317 := by
    have hnat : (563027761 : ℕ)^8365*6250000000000^6317 ≤ 2173710899027^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563027761 1250000000 2173710899027 6250000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180023177/5000000000 : ℝ), (422043109/1000000000 : ℝ), (563027761/1250000000 : ℝ)] ![(666258076581/2000000000000 : ℝ), (31907721769991/100000000000000 : ℝ), (2173710899027/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180023177/5000000000 : ℝ)|^8365 ≤ (666258076581/2000000000000 : ℝ)^6317
        have hw : |(2180023177/5000000000 : ℝ)|=(2180023177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422043109/1000000000 : ℝ)|^8365 ≤ (31907721769991/100000000000000 : ℝ)^6317
        have hw : |(422043109/1000000000 : ℝ)|=(422043109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563027761/1250000000 : ℝ)|^8365 ≤ (2173710899027/6250000000000 : ℝ)^6317
        have hw : |(563027761/1250000000 : ℝ)|=(563027761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s4_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151913273/10000000000 : ℝ)*x 0 + (2629539899/5000000000 : ℝ)*x 1 + (5400088807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151913273/10000000000 : ℝ)^8365 ≤ (2615492794571/20000000000000 : ℝ)^6317 := by
    have hnat : (2151913273 : ℕ)^8365*20000000000000^6317 ≤ 2615492794571^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151913273 10000000000 2615492794571 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629539899/5000000000 : ℝ)^8365 ≤ (10674989341093/25000000000000 : ℝ)^6317 := by
    have hnat : (2629539899 : ℕ)^8365*25000000000000^6317 ≤ 10674989341093^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629539899 5000000000 10674989341093 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400088807/10000000000 : ℝ)^8365 ≤ (5527822330733/12500000000000 : ℝ)^6317 := by
    have hnat : (5400088807 : ℕ)^8365*12500000000000^6317 ≤ 5527822330733^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400088807 10000000000 5527822330733 12500000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151913273/10000000000 : ℝ), (2629539899/5000000000 : ℝ), (5400088807/10000000000 : ℝ)] ![(2615492794571/20000000000000 : ℝ), (10674989341093/25000000000000 : ℝ), (5527822330733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151913273/10000000000 : ℝ)|^8365 ≤ (2615492794571/20000000000000 : ℝ)^6317
        have hw : |(-2151913273/10000000000 : ℝ)|=(2151913273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629539899/5000000000 : ℝ)|^8365 ≤ (10674989341093/25000000000000 : ℝ)^6317
        have hw : |(2629539899/5000000000 : ℝ)|=(2629539899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400088807/10000000000 : ℝ)|^8365 ≤ (5527822330733/12500000000000 : ℝ)^6317
        have hw : |(5400088807/10000000000 : ℝ)|=(5400088807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s4_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663830957/1250000000 : ℝ)*x 0 + (-1041271101/5000000000 : ℝ)*x 1 + (2700044399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663830957/1250000000 : ℝ)^8365 ≤ (8651054646863/20000000000000 : ℝ)^6317 := by
    have hnat : (663830957 : ℕ)^8365*20000000000000^6317 ≤ 8651054646863^6317*1250000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663830957 1250000000 8651054646863 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041271101/5000000000 : ℝ)^8365 ≤ (500885928127/4000000000000 : ℝ)^6317 := by
    have hnat : (1041271101 : ℕ)^8365*4000000000000^6317 ≤ 500885928127^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041271101 5000000000 500885928127 4000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700044399/5000000000 : ℝ)^8365 ≤ (22111289274133/50000000000000 : ℝ)^6317 := by
    have hnat : (2700044399 : ℕ)^8365*50000000000000^6317 ≤ 22111289274133^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700044399 5000000000 22111289274133 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663830957/1250000000 : ℝ), (-1041271101/5000000000 : ℝ), (2700044399/5000000000 : ℝ)] ![(8651054646863/20000000000000 : ℝ), (500885928127/4000000000000 : ℝ), (22111289274133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663830957/1250000000 : ℝ)|^8365 ≤ (8651054646863/20000000000000 : ℝ)^6317
        have hw : |(663830957/1250000000 : ℝ)|=(663830957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041271101/5000000000 : ℝ)|^8365 ≤ (500885928127/4000000000000 : ℝ)^6317
        have hw : |(-1041271101/5000000000 : ℝ)|=(1041271101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700044399/5000000000 : ℝ)|^8365 ≤ (22111289274133/50000000000000 : ℝ)^6317
        have hw : |(2700044399/5000000000 : ℝ)|=(2700044399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s4_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531064759/1000000000 : ℝ)*x 0 + (5400088697/10000000000 : ℝ)*x 1 + (-520635607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531064759/1000000000 : ℝ)^8365 ≤ (21627636261231/50000000000000 : ℝ)^6317 := by
    have hnat : (531064759 : ℕ)^8365*50000000000000^6317 ≤ 21627636261231^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531064759 1000000000 21627636261231 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400088697/10000000000 : ℝ)^8365 ≤ (44222577453/100000000000 : ℝ)^6317 := by
    have hnat : (5400088697 : ℕ)^8365*100000000000^6317 ≤ 44222577453^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400088697 10000000000 44222577453 100000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520635607/2500000000 : ℝ)^8365 ≤ (12522150002661/100000000000000 : ℝ)^6317 := by
    have hnat : (520635607 : ℕ)^8365*100000000000000^6317 ≤ 12522150002661^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520635607 2500000000 12522150002661 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531064759/1000000000 : ℝ), (5400088697/10000000000 : ℝ), (-520635607/2500000000 : ℝ)] ![(21627636261231/50000000000000 : ℝ), (44222577453/100000000000 : ℝ), (12522150002661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531064759/1000000000 : ℝ)|^8365 ≤ (21627636261231/50000000000000 : ℝ)^6317
        have hw : |(531064759/1000000000 : ℝ)|=(531064759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400088697/10000000000 : ℝ)|^8365 ≤ (44222577453/100000000000 : ℝ)^6317
        have hw : |(5400088697/10000000000 : ℝ)|=(5400088697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520635607/2500000000 : ℝ)|^8365 ≤ (12522150002661/100000000000000 : ℝ)^6317
        have hw : |(-520635607/2500000000 : ℝ)|=(520635607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s4_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090014859/2500000000 : ℝ)*x 0 + (4503420941/10000000000 : ℝ)*x 1 + (4221236051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090014859/2500000000 : ℝ)^8365 ≤ (33313036187237/100000000000000 : ℝ)^6317 := by
    have hnat : (1090014859 : ℕ)^8365*100000000000000^6317 ≤ 33313036187237^6317*2500000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090014859 2500000000 33313036187237 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503420941/10000000000 : ℝ)^8365 ≤ (17385591505489/50000000000000 : ℝ)^6317 := by
    have hnat : (4503420941 : ℕ)^8365*50000000000000^6317 ≤ 17385591505489^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503420941 10000000000 17385591505489 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221236051/10000000000 : ℝ)^8365 ≤ (6383156158309/20000000000000 : ℝ)^6317 := by
    have hnat : (4221236051 : ℕ)^8365*20000000000000^6317 ≤ 6383156158309^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221236051 10000000000 6383156158309 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090014859/2500000000 : ℝ), (4503420941/10000000000 : ℝ), (4221236051/10000000000 : ℝ)] ![(33313036187237/100000000000000 : ℝ), (17385591505489/50000000000000 : ℝ), (6383156158309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090014859/2500000000 : ℝ)|^8365 ≤ (33313036187237/100000000000000 : ℝ)^6317
        have hw : |(1090014859/2500000000 : ℝ)|=(1090014859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503420941/10000000000 : ℝ)|^8365 ≤ (17385591505489/50000000000000 : ℝ)^6317
        have hw : |(4503420941/10000000000 : ℝ)|=(4503420941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221236051/10000000000 : ℝ)|^8365 ≤ (6383156158309/20000000000000 : ℝ)^6317
        have hw : |(4221236051/10000000000 : ℝ)|=(4221236051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5361/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5361/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5361/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5361/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5361/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5361/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5361/50000 : ℝ) ^ (2091/512 : ℝ) ≤ (2739059961480227/25000000000000000000 : ℝ) := by
    have hpowers : (5361/50000 : ℝ)^2091 ≤ (2739059961480227/25000000000000000000 : ℝ)^512 := by
      have hnat : (5361 : ℕ)^2091*25000000000000000000^512 ≤ 2739059961480227^512*50000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5361 50000 2739059961480227 25000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5361/50000 : ℝ)) (X := (2739059961480227/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (20269965350629793/50000000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^2091 ≤ (20269965350629793/50000000000000000000 : ℝ)^512 := by
      have hnat : (14771 : ℕ)^2091*50000000000000000000^512 ≤ 20269965350629793^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 20269965350629793 50000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (20269965350629793/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502739059961480227/12500000000000000000 : ℝ) ≤ (5000268251111927/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (12502739059961480227/12500000000000000000 : ℝ)^512 ≤ (5000268251111927/5000000000000000 : ℝ)^2091 := by
      have hnat : (12502739059961480227 : ℕ)^512*5000000000000000^2091 ≤ 5000268251111927^2091*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502739059961480227 12500000000000000000 5000268251111927 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268251111927/5000000000000000 : ℝ)) (X := (12502739059961480227/12500000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025748085273590247/50000000000000000000 : ℝ) ≤ (10001260684571969/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50025748085273590247/50000000000000000000 : ℝ)^512 ≤ (10001260684571969/10000000000000000 : ℝ)^2091 := by
      have hnat : (50025748085273590247 : ℕ)^512*10000000000000000^2091 ≤ 10001260684571969^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025748085273590247 50000000000000000000 10001260684571969 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001260684571969/10000000000000000 : ℝ)) (X := (50025748085273590247/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020269965350629793/25000000000000000000 : ℝ) ≤ (2500496216730021/2500000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (25020269965350629793/25000000000000000000 : ℝ)^512 ≤ (2500496216730021/2500000000000000 : ℝ)^2091 := by
      have hnat : (25020269965350629793 : ℕ)^512*2500000000000000^2091 ≤ 2500496216730021^2091*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020269965350629793 25000000000000000000 2500496216730021 2500000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500496216730021/2500000000000000 : ℝ)) (X := (25020269965350629793/25000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2739059961480227/25000000000000000000 : ℝ) ≤ ((20238321465615703393/20245000000000000000 : ℝ)+2*(144836469623/80980000000000 : ℝ)*(5361/50000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (20238321465615703393/20245000000000000000 : ℝ)+2*(144836469623/80980000000000 : ℝ)*(5361/50000 : ℝ)=(5000268251111927/5000000000000000 : ℝ) by norm_num, show 1+2*(2739059961480227/25000000000000000000 : ℝ)=(12502739059961480227/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20269965350629793/50000000000000000000 : ℝ)+(2739059961480227/25000000000000000000 : ℝ) ≤ ((20238321465615703393/20245000000000000000 : ℝ)+(144836469623/80980000000000 : ℝ)*((14771/100000 : ℝ)+(5361/50000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (20238321465615703393/20245000000000000000 : ℝ)+(144836469623/80980000000000 : ℝ)*((14771/100000 : ℝ)+(5361/50000 : ℝ))=(10001260684571969/10000000000000000 : ℝ) by norm_num, show 1+(20269965350629793/50000000000000000000 : ℝ)+(2739059961480227/25000000000000000000 : ℝ)=(50025748085273590247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20269965350629793/50000000000000000000 : ℝ) ≤ ((20238321465615703393/20245000000000000000 : ℝ)+2*(144836469623/80980000000000 : ℝ)*(14771/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (20238321465615703393/20245000000000000000 : ℝ)+2*(144836469623/80980000000000 : ℝ)*(14771/100000 : ℝ)=(2500496216730021/2500000000000000 : ℝ) by norm_num, show 1+2*(20269965350629793/50000000000000000000 : ℝ)=(25020269965350629793/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20238321465615703393/20245000000000000000 : ℝ)*(X 1 0+X 2 0)+(144836469623/80980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5361/50000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (20238321465615703393/20245000000000000000 : ℝ)) (alpha := (144836469623/80980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20238321465615703393/20245000000000000000 : ℝ)*(X 0 1+X 2 1)+(144836469623/80980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5361/50000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (20238321465615703393/20245000000000000000 : ℝ)) (alpha := (144836469623/80980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20238321465615703393/20245000000000000000 : ℝ)*(X 0 2+X 1 2)+(144836469623/80980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (5361/50000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (20238321465615703393/20245000000000000000 : ℝ)) (alpha := (144836469623/80980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215190649/1000000000 : ℝ)*X 0 0+(2700245421/5000000000 : ℝ)*X 0 1+(5258679367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534665271/1000000000 : ℝ)*X 1 0+(-17374623/78125000 : ℝ)*X 1 1+(5258679713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346652713/10000000000 : ℝ)*X 2 0+(2629339997/5000000000 : ℝ)*X 2 1+(-2223951369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180023177/5000000000 : ℝ)*X 0 0+(422043109/1000000000 : ℝ)*X 0 1+(563027761/1250000000 : ℝ)*X 0 2+(2180023177/5000000000 : ℝ)*X 1 0+(422043109/1000000000 : ℝ)*X 1 1+(563027761/1250000000 : ℝ)*X 1 2+(2180023177/5000000000 : ℝ)*X 2 0+(422043109/1000000000 : ℝ)*X 2 1+(563027761/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151913273/10000000000 : ℝ)*X 0 0+(2629539899/5000000000 : ℝ)*X 0 1+(5400088807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663830957/1250000000 : ℝ)*X 1 0+(-1041271101/5000000000 : ℝ)*X 1 1+(2700044399/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531064759/1000000000 : ℝ)*X 2 0+(5400088697/10000000000 : ℝ)*X 2 1+(-520635607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090014859/2500000000 : ℝ)*X 0 0+(4503420941/10000000000 : ℝ)*X 0 1+(4221236051/10000000000 : ℝ)*X 0 2+(1090014859/2500000000 : ℝ)*X 1 0+(4503420941/10000000000 : ℝ)*X 1 1+(4221236051/10000000000 : ℝ)*X 1 2+(1090014859/2500000000 : ℝ)*X 2 0+(4503420941/10000000000 : ℝ)*X 2 1+(4221236051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3476980485556351834444922673/506125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1609715331/100000000000000 : ℝ)*(base19) + (1455437219/100000000000000 : ℝ)*(base23) + (16920533/20000000000000 : ℝ)*(lower2) + (34500563/50000000000000 : ℝ)*(upper3) + (124081689/25000000000000 : ℝ)*(upper5) + (2643874423369987/50000000000000 : ℝ)*(major0) + (2643874423369987/50000000000000 : ℝ)*(major1) + (2643874423369987/50000000000000 : ℝ)*(major2) + (7051660186816649/100000000000000 : ℝ)*(sp0) + (352586246194437/5000000000000 : ℝ)*(sp1) + (1762931269541713/25000000000000 : ℝ)*(sp2) + (352374885002647/10000000000000 : ℝ)*(sp3) + (66346787421/100000000000000 : ℝ)*(sp4) + (5520213967/25000000000000 : ℝ)*(sp7) + (1761885465441169/50000000000000 : ℝ)*(f.failure) + (7051726533604071/100000000000000 : ℝ)*(f.sum) + (5536631645437/4049000000000000000000000000 : ℝ)*base65 + (5985720086291515891/1012250000000000000000000000000000 : ℝ)*base67 + (8756598878119984109/1012250000000000000000000000000000 : ℝ)*base70 + (1619569281422515891/1012250000000000000000000000000000 : ℝ)*base71 + (1401502854293/404900000000000000000000000 : ℝ)*base73 + (35123943675822484109/1012250000000000000000000000000000 : ℝ)*base76 + (9366363849508484109/1012250000000000000000000000000000 : ℝ)*base78 + (25158286476740484109/1012250000000000000000000000000000 : ℝ)*base80 + (9389771057979/2024500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (12056389/5000000000000000000000 : ℝ)*base89 + (12056389/5000000000000000000000 : ℝ)*base91 + (12056389/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8134152827047184804109/4049000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218214581/20000000000000 : ℝ)*(base19) + (1158295557/100000000000000 : ℝ)*(base23) + (62209781/50000000000000 : ℝ)*(upper2) + (2907073/2000000000000 : ℝ)*(upper5) + (2658880679508729/50000000000000 : ℝ)*(major0) + (2658880679508729/50000000000000 : ℝ)*(major1) + (2658880679508729/50000000000000 : ℝ)*(major2) + (537424161/25000000000000 : ℝ)*(sp0) + (37189973449/100000000000000 : ℝ)*(sp1) + (12774331037/50000000000000 : ℝ)*(sp2) + (7091749146607779/100000000000000 : ℝ)*(sp4) + (709171301525807/10000000000000 : ℝ)*(sp5) + (886465573668349/12500000000000 : ℝ)*(sp6) + (354377135476619/10000000000000 : ℝ)*(sp7) + (354377135476619/10000000000000 : ℝ)*(f.failure) + (7091751296304423/100000000000000 : ℝ)*(f.sum) + (33451142405703/4049000000000000000000000000 : ℝ)*base66 + (11186793905730167497/1012250000000000000000000000000000 : ℝ)*base67 + (6076747224904582503/1012250000000000000000000000000000 : ℝ)*base70 + (8206242132822667497/1012250000000000000000000000000000 : ℝ)*base71 + (8684854176943/1012250000000000000000000000 : ℝ)*base74 + (9763428529355582503/1012250000000000000000000000000000 : ℝ)*base76 + (3674543298505667497/1012250000000000000000000000000000 : ℝ)*base77 + (9396373199222332503/1012250000000000000000000000000000 : ℝ)*base80 + (11045323839329/2024500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7112839/1000000000000000000000 : ℝ)*base89 + (7112839/1000000000000000000000 : ℝ)*base91 + (7112839/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1172_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5361/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1172_s5_0 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076240521/5000000000 : ℝ)*x 0 + (5394136227/10000000000 : ℝ)*x 1 + (2632328323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076240521/5000000000 : ℝ)^8365 ≤ (523281328563/4000000000000 : ℝ)^6317 := by
    have hnat : (1076240521 : ℕ)^8365*4000000000000^6317 ≤ 523281328563^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076240521 5000000000 523281328563 4000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394136227/10000000000 : ℝ)^8365 ≤ (22079019554761/50000000000000 : ℝ)^6317 := by
    have hnat : (5394136227 : ℕ)^8365*50000000000000^6317 ≤ 22079019554761^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394136227 10000000000 22079019554761 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632328323/5000000000 : ℝ)^8365 ≤ (21379963829783/50000000000000 : ℝ)^6317 := by
    have hnat : (2632328323 : ℕ)^8365*50000000000000^6317 ≤ 21379963829783^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632328323 5000000000 21379963829783 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076240521/5000000000 : ℝ), (5394136227/10000000000 : ℝ), (2632328323/5000000000 : ℝ)] ![(523281328563/4000000000000 : ℝ), (22079019554761/50000000000000 : ℝ), (21379963829783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076240521/5000000000 : ℝ)|^8365 ≤ (523281328563/4000000000000 : ℝ)^6317
        have hw : |(-1076240521/5000000000 : ℝ)|=(1076240521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394136227/10000000000 : ℝ)|^8365 ≤ (22079019554761/50000000000000 : ℝ)^6317
        have hw : |(5394136227/10000000000 : ℝ)|=(5394136227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632328323/5000000000 : ℝ)|^8365 ≤ (21379963829783/50000000000000 : ℝ)^6317
        have hw : |(2632328323/5000000000 : ℝ)|=(2632328323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s5_1 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672527239/5000000000 : ℝ)*x 0 + (-2218171027/10000000000 : ℝ)*x 1 + (329041053/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672527239/5000000000 : ℝ)^8365 ≤ (43626762619449/100000000000000 : ℝ)^6317 := by
    have hnat : (2672527239 : ℕ)^8365*100000000000000^6317 ≤ 43626762619449^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672527239 5000000000 43626762619449 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218171027/10000000000 : ℝ)^8365 ≤ (6806653766427/50000000000000 : ℝ)^6317 := by
    have hnat : (2218171027 : ℕ)^8365*50000000000000^6317 ≤ 6806653766427^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218171027 10000000000 6806653766427 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329041053/625000000 : ℝ)^8365 ≤ (42759929832133/100000000000000 : ℝ)^6317 := by
    have hnat : (329041053 : ℕ)^8365*100000000000000^6317 ≤ 42759929832133^6317*625000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329041053 625000000 42759929832133 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672527239/5000000000 : ℝ), (-2218171027/10000000000 : ℝ), (329041053/625000000 : ℝ)] ![(43626762619449/100000000000000 : ℝ), (6806653766427/50000000000000 : ℝ), (42759929832133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672527239/5000000000 : ℝ)|^8365 ≤ (43626762619449/100000000000000 : ℝ)^6317
        have hw : |(2672527239/5000000000 : ℝ)|=(2672527239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2218171027/10000000000 : ℝ)|^8365 ≤ (6806653766427/50000000000000 : ℝ)^6317
        have hw : |(-2218171027/10000000000 : ℝ)|=(2218171027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329041053/625000000 : ℝ)|^8365 ≤ (42759929832133/100000000000000 : ℝ)^6317
        have hw : |(329041053/625000000 : ℝ)|=(329041053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s5_2 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069010939/2000000000 : ℝ)*x 0 + (526465677/1000000000 : ℝ)*x 1 + (-2218170841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069010939/2000000000 : ℝ)^8365 ≤ (21813382482421/50000000000000 : ℝ)^6317 := by
    have hnat : (1069010939 : ℕ)^8365*50000000000000^6317 ≤ 21813382482421^6317*2000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069010939 2000000000 21813382482421 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526465677/1000000000 : ℝ)^8365 ≤ (42759928993221/100000000000000 : ℝ)^6317 := by
    have hnat : (526465677 : ℕ)^8365*100000000000000^6317 ≤ 42759928993221^6317*1000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526465677 1000000000 42759928993221 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218170841/10000000000 : ℝ)^8365 ≤ (2722661204251/20000000000000 : ℝ)^6317 := by
    have hnat : (2218170841 : ℕ)^8365*20000000000000^6317 ≤ 2722661204251^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218170841 10000000000 2722661204251 20000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069010939/2000000000 : ℝ), (526465677/1000000000 : ℝ), (-2218170841/10000000000 : ℝ)] ![(21813382482421/50000000000000 : ℝ), (42759928993221/100000000000000 : ℝ), (2722661204251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069010939/2000000000 : ℝ)|^8365 ≤ (21813382482421/50000000000000 : ℝ)^6317
        have hw : |(1069010939/2000000000 : ℝ)|=(1069010939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526465677/1000000000 : ℝ)|^8365 ≤ (42759928993221/100000000000000 : ℝ)^6317
        have hw : |(526465677/1000000000 : ℝ)|=(526465677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2218170841/10000000000 : ℝ)|^8365 ≤ (2722661204251/20000000000000 : ℝ)^6317
        have hw : |(-2218170841/10000000000 : ℝ)|=(2218170841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s5_3 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360382337/10000000000 : ℝ)*x 0 + (4232726573/10000000000 : ℝ)*x 1 + (4491839639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360382337/10000000000 : ℝ)^8365 ≤ (16658151602437/50000000000000 : ℝ)^6317 := by
    have hnat : (4360382337 : ℕ)^8365*50000000000000^6317 ≤ 16658151602437^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360382337 10000000000 16658151602437 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232726573/10000000000 : ℝ)^8365 ≤ (16015437323283/50000000000000 : ℝ)^6317 := by
    have hnat : (4232726573 : ℕ)^8365*50000000000000^6317 ≤ 16015437323283^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232726573 10000000000 16015437323283 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491839639/10000000000 : ℝ)^8365 ≤ (1732641106481/5000000000000 : ℝ)^6317 := by
    have hnat : (4491839639 : ℕ)^8365*5000000000000^6317 ≤ 1732641106481^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491839639 10000000000 1732641106481 5000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360382337/10000000000 : ℝ), (4232726573/10000000000 : ℝ), (4491839639/10000000000 : ℝ)] ![(16658151602437/50000000000000 : ℝ), (16015437323283/50000000000000 : ℝ), (1732641106481/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360382337/10000000000 : ℝ)|^8365 ≤ (16658151602437/50000000000000 : ℝ)^6317
        have hw : |(4360382337/10000000000 : ℝ)|=(4360382337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232726573/10000000000 : ℝ)|^8365 ≤ (16015437323283/50000000000000 : ℝ)^6317
        have hw : |(4232726573/10000000000 : ℝ)|=(4232726573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491839639/10000000000 : ℝ)|^8365 ≤ (1732641106481/5000000000000 : ℝ)^6317
        have hw : |(4491839639/10000000000 : ℝ)|=(4491839639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s5_4 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1076242903/5000000000 : ℝ)*x 0 + (5264990629/10000000000 : ℝ)*x 1 + (5393801321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076242903/5000000000 : ℝ)^8365 ≤ (6541035777513/50000000000000 : ℝ)^6317 := by
    have hnat : (1076242903 : ℕ)^8365*50000000000000^6317 ≤ 6541035777513^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076242903 5000000000 6541035777513 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264990629/10000000000 : ℝ)^8365 ≤ (10690879944827/25000000000000 : ℝ)^6317 := by
    have hnat : (5264990629 : ℕ)^8365*25000000000000^6317 ≤ 10690879944827^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264990629 10000000000 10690879944827 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393801321/10000000000 : ℝ)^8365 ≤ (44154408650867/100000000000000 : ℝ)^6317 := by
    have hnat : (5393801321 : ℕ)^8365*100000000000000^6317 ≤ 44154408650867^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393801321 10000000000 44154408650867 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1076242903/5000000000 : ℝ), (5264990629/10000000000 : ℝ), (5393801321/10000000000 : ℝ)] ![(6541035777513/50000000000000 : ℝ), (10690879944827/25000000000000 : ℝ), (44154408650867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1076242903/5000000000 : ℝ)|^8365 ≤ (6541035777513/50000000000000 : ℝ)^6317
        have hw : |(-1076242903/5000000000 : ℝ)|=(1076242903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264990629/10000000000 : ℝ)|^8365 ≤ (10690879944827/25000000000000 : ℝ)^6317
        have hw : |(5264990629/10000000000 : ℝ)|=(5264990629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393801321/10000000000 : ℝ)|^8365 ≤ (44154408650867/100000000000000 : ℝ)^6317
        have hw : |(5393801321/10000000000 : ℝ)|=(5393801321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s5_5 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656089441/5000000000 : ℝ)*x 0 + (-2089026209/10000000000 : ℝ)*x 1 + (2696900661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656089441/5000000000 : ℝ)^8365 ≤ (10817947321481/25000000000000 : ℝ)^6317 := by
    have hnat : (2656089441 : ℕ)^8365*25000000000000^6317 ≤ 10817947321481^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656089441 5000000000 10817947321481 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089026209/10000000000 : ℝ)^8365 ≤ (12573802036203/100000000000000 : ℝ)^6317 := by
    have hnat : (2089026209 : ℕ)^8365*100000000000000^6317 ≤ 12573802036203^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089026209 10000000000 12573802036203 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696900661/5000000000 : ℝ)^8365 ≤ (44154408661707/100000000000000 : ℝ)^6317 := by
    have hnat : (2696900661 : ℕ)^8365*100000000000000^6317 ≤ 44154408661707^6317*5000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696900661 5000000000 44154408661707 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656089441/5000000000 : ℝ), (-2089026209/10000000000 : ℝ), (2696900661/5000000000 : ℝ)] ![(10817947321481/25000000000000 : ℝ), (12573802036203/100000000000000 : ℝ), (44154408661707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656089441/5000000000 : ℝ)|^8365 ≤ (10817947321481/25000000000000 : ℝ)^6317
        have hw : |(2656089441/5000000000 : ℝ)|=(2656089441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089026209/10000000000 : ℝ)|^8365 ≤ (12573802036203/100000000000000 : ℝ)^6317
        have hw : |(-2089026209/10000000000 : ℝ)|=(2089026209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696900661/5000000000 : ℝ)|^8365 ≤ (44154408661707/100000000000000 : ℝ)^6317
        have hw : |(2696900661/5000000000 : ℝ)|=(2696900661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s5_6 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312178873/10000000000 : ℝ)*x 0 + (5393801331/10000000000 : ℝ)*x 1 + (-2089026209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312178873/10000000000 : ℝ)^8365 ≤ (10817947297211/25000000000000 : ℝ)^6317 := by
    have hnat : (5312178873 : ℕ)^8365*25000000000000^6317 ≤ 10817947297211^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312178873 10000000000 10817947297211 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393801331/10000000000 : ℝ)^8365 ≤ (11038602189817/25000000000000 : ℝ)^6317 := by
    have hnat : (5393801331 : ℕ)^8365*25000000000000^6317 ≤ 11038602189817^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393801331 10000000000 11038602189817 25000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089026209/10000000000 : ℝ)^8365 ≤ (12573802036203/100000000000000 : ℝ)^6317 := by
    have hnat : (2089026209 : ℕ)^8365*100000000000000^6317 ≤ 12573802036203^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089026209 10000000000 12573802036203 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312178873/10000000000 : ℝ), (5393801331/10000000000 : ℝ), (-2089026209/10000000000 : ℝ)] ![(10817947297211/25000000000000 : ℝ), (11038602189817/25000000000000 : ℝ), (12573802036203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312178873/10000000000 : ℝ)|^8365 ≤ (10817947297211/25000000000000 : ℝ)^6317
        have hw : |(5312178873/10000000000 : ℝ)|=(5312178873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393801331/10000000000 : ℝ)|^8365 ≤ (11038602189817/25000000000000 : ℝ)^6317
        have hw : |(5393801331/10000000000 : ℝ)|=(5393801331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089026209/10000000000 : ℝ)|^8365 ≤ (12573802036203/100000000000000 : ℝ)^6317
        have hw : |(-2089026209/10000000000 : ℝ)|=(2089026209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1172_s5_7 (p : ℝ) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360392051/10000000000 : ℝ)*x 0 + (140349121/312500000 : ℝ)*x 1 + (4233397487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360392051/10000000000 : ℝ)^8365 ≤ (33316401489493/100000000000000 : ℝ)^6317 := by
    have hnat : (4360392051 : ℕ)^8365*100000000000000^6317 ≤ 33316401489493^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360392051 10000000000 33316401489493 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140349121/312500000 : ℝ)^8365 ≤ (17323000283099/50000000000000 : ℝ)^6317 := by
    have hnat : (140349121 : ℕ)^8365*50000000000000^6317 ≤ 17323000283099^6317*312500000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140349121 312500000 17323000283099 50000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233397487/10000000000 : ℝ)^8365 ≤ (32037597933779/100000000000000 : ℝ)^6317 := by
    have hnat : (4233397487 : ℕ)^8365*100000000000000^6317 ≤ 32037597933779^6317*10000000000^8365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233397487 10000000000 32037597933779 100000000000000 8365 6317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8365/2048 : ℝ)) 8365 6317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360392051/10000000000 : ℝ), (140349121/312500000 : ℝ), (4233397487/10000000000 : ℝ)] ![(33316401489493/100000000000000 : ℝ), (17323000283099/50000000000000 : ℝ), (32037597933779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360392051/10000000000 : ℝ)|^8365 ≤ (33316401489493/100000000000000 : ℝ)^6317
        have hw : |(4360392051/10000000000 : ℝ)|=(4360392051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140349121/312500000 : ℝ)|^8365 ≤ (17323000283099/50000000000000 : ℝ)^6317
        have hw : |(140349121/312500000 : ℝ)|=(140349121/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233397487/10000000000 : ℝ)|^8365 ≤ (32037597933779/100000000000000 : ℝ)^6317
        have hw : |(4233397487/10000000000 : ℝ)|=(4233397487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1172_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5679/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14101/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11231/100000 : ℝ) ^ (2091/512 : ℝ) ≤ (13241088676738117/100000000000000000000 : ℝ) := by
    have hpowers : (11231/100000 : ℝ)^2091 ≤ (13241088676738117/100000000000000000000 : ℝ)^512 := by
      have hnat : (11231 : ℕ)^2091*100000000000000000000^512 ≤ 13241088676738117^512*100000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11231 100000 13241088676738117 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11231/100000 : ℝ)) (X := (13241088676738117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (2091/512 : ℝ) ≤ (34849820055748993/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^2091 ≤ (34849820055748993/100000000000000000000 : ℝ)^512 := by
      have hnat : (7117 : ℕ)^2091*100000000000000000000^512 ≤ 34849820055748993^512*50000^2091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 34849820055748993 100000000000000000000 2091 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (34849820055748993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013241088676738117/50000000000000000000 : ℝ) ≤ (2500162093726423/2500000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50013241088676738117/50000000000000000000 : ℝ)^512 ≤ (2500162093726423/2500000000000000 : ℝ)^2091 := by
      have hnat : (50013241088676738117 : ℕ)^512*2500000000000000^2091 ≤ 2500162093726423^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013241088676738117 50000000000000000000 2500162093726423 2500000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500162093726423/2500000000000000 : ℝ)) (X := (50013241088676738117/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004809090873248711/10000000000000000000 : ℝ) ≤ (10001177335037689/10000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (10004809090873248711/10000000000000000000 : ℝ)^512 ≤ (10001177335037689/10000000000000000 : ℝ)^2091 := by
      have hnat : (10004809090873248711 : ℕ)^512*10000000000000000^2091 ≤ 10001177335037689^2091*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004809090873248711 10000000000000000000 10001177335037689 10000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001177335037689/10000000000000000 : ℝ)) (X := (10004809090873248711/10000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034849820055748993/50000000000000000000 : ℝ) ≤ (5000853147584843/5000000000000000 : ℝ) ^ (2091/512 : ℝ) := by
    have hpowers : (50034849820055748993/50000000000000000000 : ℝ)^512 ≤ (5000853147584843/5000000000000000 : ℝ)^2091 := by
      have hnat : (50034849820055748993 : ℕ)^512*5000000000000000^2091 ≤ 5000853147584843^2091*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034849820055748993 50000000000000000000 5000853147584843 5000000000000000 512 2091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000853147584843/5000000000000000 : ℝ)) (X := (50034849820055748993/50000000000000000000 : ℝ)) (by norm_num) 2091 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13241088676738117/100000000000000000000 : ℝ) ≤ ((454849478293286007/455000000000000000 : ℝ)+2*(16029094909/9100000000000 : ℝ)*(11231/100000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (454849478293286007/455000000000000000 : ℝ)+2*(16029094909/9100000000000 : ℝ)*(11231/100000 : ℝ)=(2500162093726423/2500000000000000 : ℝ) by norm_num, show 1+2*(13241088676738117/100000000000000000000 : ℝ)=(50013241088676738117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34849820055748993/100000000000000000000 : ℝ)+(13241088676738117/100000000000000000000 : ℝ) ≤ ((454849478293286007/455000000000000000 : ℝ)+(16029094909/9100000000000 : ℝ)*((7117/50000 : ℝ)+(11231/100000 : ℝ)))^(2091/512 : ℝ) := by
    rw [show (454849478293286007/455000000000000000 : ℝ)+(16029094909/9100000000000 : ℝ)*((7117/50000 : ℝ)+(11231/100000 : ℝ))=(10001177335037689/10000000000000000 : ℝ) by norm_num, show 1+(34849820055748993/100000000000000000000 : ℝ)+(13241088676738117/100000000000000000000 : ℝ)=(10004809090873248711/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34849820055748993/100000000000000000000 : ℝ) ≤ ((454849478293286007/455000000000000000 : ℝ)+2*(16029094909/9100000000000 : ℝ)*(7117/50000 : ℝ))^(2091/512 : ℝ) := by
    rw [show (454849478293286007/455000000000000000 : ℝ)+2*(16029094909/9100000000000 : ℝ)*(7117/50000 : ℝ)=(5000853147584843/5000000000000000 : ℝ) by norm_num, show 1+2*(34849820055748993/100000000000000000000 : ℝ)=(50034849820055748993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (454849478293286007/455000000000000000 : ℝ)*(X 1 0+X 2 0)+(16029094909/9100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (454849478293286007/455000000000000000 : ℝ)) (alpha := (16029094909/9100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (454849478293286007/455000000000000000 : ℝ)*(X 0 1+X 2 1)+(16029094909/9100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (454849478293286007/455000000000000000 : ℝ)) (alpha := (16029094909/9100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (454849478293286007/455000000000000000 : ℝ)*(X 0 2+X 1 2)+(16029094909/9100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2091/512 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (454849478293286007/455000000000000000 : ℝ)) (alpha := (16029094909/9100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1076240521/5000000000 : ℝ)*X 0 0+(5394136227/10000000000 : ℝ)*X 0 1+(2632328323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672527239/5000000000 : ℝ)*X 1 0+(-2218171027/10000000000 : ℝ)*X 1 1+(329041053/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069010939/2000000000 : ℝ)*X 2 0+(526465677/1000000000 : ℝ)*X 2 1+(-2218170841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360382337/10000000000 : ℝ)*X 0 0+(4232726573/10000000000 : ℝ)*X 0 1+(4491839639/10000000000 : ℝ)*X 0 2+(4360382337/10000000000 : ℝ)*X 1 0+(4232726573/10000000000 : ℝ)*X 1 1+(4491839639/10000000000 : ℝ)*X 1 2+(4360382337/10000000000 : ℝ)*X 2 0+(4232726573/10000000000 : ℝ)*X 2 1+(4491839639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1076242903/5000000000 : ℝ)*X 0 0+(5264990629/10000000000 : ℝ)*X 0 1+(5393801321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656089441/5000000000 : ℝ)*X 1 0+(-2089026209/10000000000 : ℝ)*X 1 1+(2696900661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312178873/10000000000 : ℝ)*X 2 0+(5393801331/10000000000 : ℝ)*X 2 1+(-2089026209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360392051/10000000000 : ℝ)*X 0 0+(140349121/312500000 : ℝ)*X 0 1+(4233397487/10000000000 : ℝ)*X 0 2+(4360392051/10000000000 : ℝ)*X 1 0+(140349121/312500000 : ℝ)*X 1 1+(4233397487/10000000000 : ℝ)*X 1 2+(4360392051/10000000000 : ℝ)*X 2 0+(140349121/312500000 : ℝ)*X 2 1+(4233397487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1172_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106725704739091254766171977/11375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (472267403/20000000000000 : ℝ)*(base19) + (2668648203/100000000000000 : ℝ)*(base23) + (667443/20000000000000 : ℝ)*(lower2) + (19555419/6250000000000 : ℝ)*(upper3) + (164933271/25000000000000 : ℝ)*(upper5) + (2895684846607921/50000000000000 : ℝ)*(major0) + (2895684846607921/50000000000000 : ℝ)*(major1) + (2895684846607921/50000000000000 : ℝ)*(major2) + (772327933676233/10000000000000 : ℝ)*(sp0) + (3861675705629271/50000000000000 : ℝ)*(sp1) + (3861675551973677/50000000000000 : ℝ)*(sp2) + (3859354718049457/100000000000000 : ℝ)*(sp3) + (74435833227/100000000000000 : ℝ)*(sp4) + (15291518673/50000000000000 : ℝ)*(sp7) + (3859385301086803/100000000000000 : ℝ)*(f.failure) + (7723353772595557/100000000000000 : ℝ)*(f.sum) + (2497340645637/455000000000000000000000000 : ℝ)*base66 + (8501910052611447/22750000000000000000000000000000 : ℝ)*base67 + (82013932591111447/22750000000000000000000000000000 : ℝ)*base69 + (76453487723861447/22750000000000000000000000000000 : ℝ)*base71 + (2560056073867/455000000000000000000000000 : ℝ)*base74 + (192270497896361447/22750000000000000000000000000000 : ℝ)*base75 + (122006359770361447/22750000000000000000000000000000 : ℝ)*base77 + (421279550623361447/22750000000000000000000000000000 : ℝ)*base79 + (682944870627/455000000000000000000000000 : ℝ)*base82 + (85448943/10000000000000000000000 : ℝ)*base89 + (85448943/10000000000000000000000 : ℝ)*base91 + (85448943/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31064598186132045395639307/5687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100245073/10000000000000 : ℝ)*(base19) + (136151381/12500000000000 : ℝ)*(base23) + (22523049/20000000000000 : ℝ)*(upper3) + (4484331/10000000000000 : ℝ)*(lower4) + (107212653/100000000000000 : ℝ)*(upper5) + (2910672598088533/50000000000000 : ℝ)*(major0) + (2910672598088533/50000000000000 : ℝ)*(major1) + (2910672598088533/50000000000000 : ℝ)*(major2) + (338680587/1250000000000 : ℝ)*(sp1) + (29598325749/100000000000000 : ℝ)*(sp2) + (3881664574216961/50000000000000 : ℝ)*(sp4) + (7763301051536233/100000000000000 : ℝ)*(sp5) + (3881649230448563/50000000000000 : ℝ)*(sp6) + (484920132732077/12500000000000 : ℝ)*(sp7) + (484920132732077/12500000000000 : ℝ)*(f.failure) + (3881664574216961/50000000000000 : ℝ)*(f.sum) + (617050093887/227500000000000000000000000 : ℝ)*base65 + (432082802053407731/22750000000000000000000000000000 : ℝ)*base67 + (455394434397407731/22750000000000000000000000000000 : ℝ)*base69 + (311711284605407731/22750000000000000000000000000000 : ℝ)*base71 + (9377483569/455000000000000000000000000 : ℝ)*base73 + (208368765871407731/22750000000000000000000000000000 : ℝ)*base75 + (32121799693842269/22750000000000000000000000000000 : ℝ)*base78 + (307974078723907731/22750000000000000000000000000000 : ℝ)*base79 + (1445031151199/455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11535663/1250000000000000000000 : ℝ)*base90 + (11535663/1250000000000000000000 : ℝ)*base92 + (11535663/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1172_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1172_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1172_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1172_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1172_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1172_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2091/512 : ℝ) ≤ p) (hpb : p ≤ (8365/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150059381/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1172_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
