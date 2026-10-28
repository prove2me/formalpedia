-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:11:32.021086+00:00
-- url     : https://prove2.me/submissions/c42cffc5-8eef-48a8-ad45-1b65de6a0aa5

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
theorem support_rectangle_w1222_s6_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064593533/5000000000 : ℝ)*x 0 + (2695894869/5000000000 : ℝ)*x 1 + (263336669/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064593533/5000000000 : ℝ)^8415 ≤ (3236443710077/25000000000000 : ℝ)^6367 := by
    have hnat : (1064593533 : ℕ)^8415*25000000000000^6367 ≤ 3236443710077^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064593533 5000000000 3236443710077 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695894869/5000000000 : ℝ)^8415 ≤ (2762629045933/6250000000000 : ℝ)^6367 := by
    have hnat : (2695894869 : ℕ)^8415*6250000000000^6367 ≤ 2762629045933^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695894869 5000000000 2762629045933 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263336669/500000000 : ℝ)^8415 ≤ (42852160414289/100000000000000 : ℝ)^6367 := by
    have hnat : (263336669 : ℕ)^8415*100000000000000^6367 ≤ 42852160414289^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263336669 500000000 42852160414289 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064593533/5000000000 : ℝ), (2695894869/5000000000 : ℝ), (263336669/500000000 : ℝ)] ![(3236443710077/25000000000000 : ℝ), (2762629045933/6250000000000 : ℝ), (42852160414289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064593533/5000000000 : ℝ)|^8415 ≤ (3236443710077/25000000000000 : ℝ)^6367
        have hw : |(-1064593533/5000000000 : ℝ)|=(1064593533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695894869/5000000000 : ℝ)|^8415 ≤ (2762629045933/6250000000000 : ℝ)^6367
        have hw : |(2695894869/5000000000 : ℝ)|=(2695894869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263336669/500000000 : ℝ)|^8415 ≤ (42852160414289/100000000000000 : ℝ)^6367
        have hw : |(263336669/500000000 : ℝ)|=(263336669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s6_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672233471/5000000000 : ℝ)*x 0 + (-2192601291/10000000000 : ℝ)*x 1 + (1316683423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672233471/5000000000 : ℝ)^8415 ≤ (21845023748709/50000000000000 : ℝ)^6367 := by
    have hnat : (2672233471 : ℕ)^8415*50000000000000^6367 ≤ 21845023748709^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672233471 5000000000 21845023748709 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192601291/10000000000 : ℝ)^8415 ≤ (6728894360051/50000000000000 : ℝ)^6367 := by
    have hnat : (2192601291 : ℕ)^8415*50000000000000^6367 ≤ 6728894360051^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192601291 10000000000 6728894360051 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316683423/2500000000 : ℝ)^8415 ≤ (42852163769387/100000000000000 : ℝ)^6367 := by
    have hnat : (1316683423 : ℕ)^8415*100000000000000^6367 ≤ 42852163769387^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316683423 2500000000 42852163769387 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672233471/5000000000 : ℝ), (-2192601291/10000000000 : ℝ), (1316683423/2500000000 : ℝ)] ![(21845023748709/50000000000000 : ℝ), (6728894360051/50000000000000 : ℝ), (42852163769387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672233471/5000000000 : ℝ)|^8415 ≤ (21845023748709/50000000000000 : ℝ)^6367
        have hw : |(2672233471/5000000000 : ℝ)|=(2672233471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192601291/10000000000 : ℝ)|^8415 ≤ (6728894360051/50000000000000 : ℝ)^6367
        have hw : |(-2192601291/10000000000 : ℝ)|=(2192601291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316683423/2500000000 : ℝ)|^8415 ≤ (42852163769387/100000000000000 : ℝ)^6367
        have hw : |(1316683423/2500000000 : ℝ)|=(1316683423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s6_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068893411/2000000000 : ℝ)*x 0 + (5266733481/10000000000 : ℝ)*x 1 + (-109630071/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068893411/2000000000 : ℝ)^8415 ≤ (21845024359153/50000000000000 : ℝ)^6367 := by
    have hnat : (1068893411 : ℕ)^8415*50000000000000^6367 ≤ 21845024359153^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068893411 2000000000 21845024359153 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266733481/10000000000 : ℝ)^8415 ≤ (21426080750197/50000000000000 : ℝ)^6367 := by
    have hnat : (5266733481 : ℕ)^8415*50000000000000^6367 ≤ 21426080750197^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266733481 10000000000 21426080750197 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109630071/500000000 : ℝ)^8415 ≤ (13457789766563/100000000000000 : ℝ)^6367 := by
    have hnat : (109630071 : ℕ)^8415*100000000000000^6367 ≤ 13457789766563^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109630071 500000000 13457789766563 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068893411/2000000000 : ℝ), (5266733481/10000000000 : ℝ), (-109630071/500000000 : ℝ)] ![(21845024359153/50000000000000 : ℝ), (21426080750197/50000000000000 : ℝ), (13457789766563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068893411/2000000000 : ℝ)|^8415 ≤ (21845024359153/50000000000000 : ℝ)^6367
        have hw : |(1068893411/2000000000 : ℝ)|=(1068893411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266733481/10000000000 : ℝ)|^8415 ≤ (21426080750197/50000000000000 : ℝ)^6367
        have hw : |(5266733481/10000000000 : ℝ)|=(5266733481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109630071/500000000 : ℝ)|^8415 ≤ (13457789766563/100000000000000 : ℝ)^6367
        have hw : |(-109630071/500000000 : ℝ)|=(109630071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s6_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353512709/10000000000 : ℝ)*x 0 + (4228950341/10000000000 : ℝ)*x 1 + (4481656553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353512709/10000000000 : ℝ)^8415 ≤ (6663456250709/20000000000000 : ℝ)^6367 := by
    have hnat : (4353512709 : ℕ)^8415*20000000000000^6367 ≤ 6663456250709^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353512709 10000000000 6663456250709 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228950341/10000000000 : ℝ)^8415 ≤ (3206321742841/10000000000000 : ℝ)^6367 := by
    have hnat : (4228950341 : ℕ)^8415*10000000000000^6367 ≤ 3206321742841^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228950341 10000000000 3206321742841 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481656553/10000000000 : ℝ)^8415 ≤ (34619501302191/100000000000000 : ℝ)^6367 := by
    have hnat : (4481656553 : ℕ)^8415*100000000000000^6367 ≤ 34619501302191^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481656553 10000000000 34619501302191 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353512709/10000000000 : ℝ), (4228950341/10000000000 : ℝ), (4481656553/10000000000 : ℝ)] ![(6663456250709/20000000000000 : ℝ), (3206321742841/10000000000000 : ℝ), (34619501302191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353512709/10000000000 : ℝ)|^8415 ≤ (6663456250709/20000000000000 : ℝ)^6367
        have hw : |(4353512709/10000000000 : ℝ)|=(4353512709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228950341/10000000000 : ℝ)|^8415 ≤ (3206321742841/10000000000000 : ℝ)^6367
        have hw : |(4228950341/10000000000 : ℝ)|=(4228950341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481656553/10000000000 : ℝ)|^8415 ≤ (34619501302191/100000000000000 : ℝ)^6367
        have hw : |(4481656553/10000000000 : ℝ)|=(4481656553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s6_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129191759/10000000000 : ℝ)*x 0 + (5267049687/10000000000 : ℝ)*x 1 + (5391472323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129191759/10000000000 : ℝ)^8415 ≤ (1618226569089/12500000000000 : ℝ)^6367 := by
    have hnat : (2129191759 : ℕ)^8415*12500000000000^6367 ≤ 1618226569089^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129191759 10000000000 1618226569089 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267049687/10000000000 : ℝ)^8415 ≤ (21427780930443/50000000000000 : ℝ)^6367 := by
    have hnat : (5267049687 : ℕ)^8415*50000000000000^6367 ≤ 21427780930443^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267049687 10000000000 21427780930443 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391472323/10000000000 : ℝ)^8415 ≤ (690603524629/1562500000000 : ℝ)^6367 := by
    have hnat : (5391472323 : ℕ)^8415*1562500000000^6367 ≤ 690603524629^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391472323 10000000000 690603524629 1562500000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129191759/10000000000 : ℝ), (5267049687/10000000000 : ℝ), (5391472323/10000000000 : ℝ)] ![(1618226569089/12500000000000 : ℝ), (21427780930443/50000000000000 : ℝ), (690603524629/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129191759/10000000000 : ℝ)|^8415 ≤ (1618226569089/12500000000000 : ℝ)^6367
        have hw : |(-2129191759/10000000000 : ℝ)|=(2129191759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267049687/10000000000 : ℝ)|^8415 ≤ (21427780930443/50000000000000 : ℝ)^6367
        have hw : |(5267049687/10000000000 : ℝ)|=(5267049687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391472323/10000000000 : ℝ)|^8415 ≤ (690603524629/1562500000000 : ℝ)^6367
        have hw : |(5391472323/10000000000 : ℝ)|=(5391472323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s6_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664075241/1250000000 : ℝ)*x 0 + (-516965619/2500000000 : ℝ)*x 1 + (2695736189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664075241/1250000000 : ℝ)^8415 ≤ (433460983033/1000000000000 : ℝ)^6367 := by
    have hnat : (664075241 : ℕ)^8415*1000000000000^6367 ≤ 433460983033^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664075241 1250000000 433460983033 1000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516965619/2500000000 : ℝ)^8415 ≤ (2491055101009/20000000000000 : ℝ)^6367 := by
    have hnat : (516965619 : ℕ)^8415*20000000000000^6367 ≤ 2491055101009^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516965619 2500000000 2491055101009 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695736189/5000000000 : ℝ)^8415 ≤ (4419862617217/10000000000000 : ℝ)^6367 := by
    have hnat : (2695736189 : ℕ)^8415*10000000000000^6367 ≤ 4419862617217^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695736189 5000000000 4419862617217 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664075241/1250000000 : ℝ), (-516965619/2500000000 : ℝ), (2695736189/5000000000 : ℝ)] ![(433460983033/1000000000000 : ℝ), (2491055101009/20000000000000 : ℝ), (4419862617217/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664075241/1250000000 : ℝ)|^8415 ≤ (433460983033/1000000000000 : ℝ)^6367
        have hw : |(664075241/1250000000 : ℝ)|=(664075241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516965619/2500000000 : ℝ)|^8415 ≤ (2491055101009/20000000000000 : ℝ)^6367
        have hw : |(-516965619/2500000000 : ℝ)|=(516965619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695736189/5000000000 : ℝ)|^8415 ≤ (4419862617217/10000000000000 : ℝ)^6367
        have hw : |(2695736189/5000000000 : ℝ)|=(2695736189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s6_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265630093/500000000 : ℝ)*x 0 + (168483513/312500000 : ℝ)*x 1 + (-2067862517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265630093/500000000 : ℝ)^8415 ≤ (21673048785009/50000000000000 : ℝ)^6367 := by
    have hnat : (265630093 : ℕ)^8415*50000000000000^6367 ≤ 21673048785009^6367*500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265630093 500000000 21673048785009 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168483513/312500000 : ℝ)^8415 ≤ (11049656645973/25000000000000 : ℝ)^6367 := by
    have hnat : (168483513 : ℕ)^8415*25000000000000^6367 ≤ 11049656645973^6367*312500000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168483513 312500000 11049656645973 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067862517/10000000000 : ℝ)^8415 ≤ (6227637915717/50000000000000 : ℝ)^6367 := by
    have hnat : (2067862517 : ℕ)^8415*50000000000000^6367 ≤ 6227637915717^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067862517 10000000000 6227637915717 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265630093/500000000 : ℝ), (168483513/312500000 : ℝ), (-2067862517/10000000000 : ℝ)] ![(21673048785009/50000000000000 : ℝ), (11049656645973/25000000000000 : ℝ), (6227637915717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265630093/500000000 : ℝ)|^8415 ≤ (21673048785009/50000000000000 : ℝ)^6367
        have hw : |(265630093/500000000 : ℝ)|=(265630093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168483513/312500000 : ℝ)|^8415 ≤ (11049656645973/25000000000000 : ℝ)^6367
        have hw : |(168483513/312500000 : ℝ)|=(168483513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067862517/10000000000 : ℝ)|^8415 ≤ (6227637915717/50000000000000 : ℝ)^6367
        have hw : |(-2067862517/10000000000 : ℝ)|=(2067862517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s6_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353522219/10000000000 : ℝ)*x 0 + (1120254389/2500000000 : ℝ)*x 1 + (16918367/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353522219/10000000000 : ℝ)^8415 ≤ (3331737744349/10000000000000 : ℝ)^6367 := by
    have hnat : (4353522219 : ℕ)^8415*10000000000000^6367 ≤ 3331737744349^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353522219 10000000000 3331737744349 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120254389/2500000000 : ℝ)^8415 ≤ (2163311103531/6250000000000 : ℝ)^6367 := by
    have hnat : (1120254389 : ℕ)^8415*6250000000000^6367 ≤ 2163311103531^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120254389 2500000000 2163311103531 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16918367/40000000 : ℝ)^8415 ≤ (32069644889081/100000000000000 : ℝ)^6367 := by
    have hnat : (16918367 : ℕ)^8415*100000000000000^6367 ≤ 32069644889081^6367*40000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16918367 40000000 32069644889081 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353522219/10000000000 : ℝ), (1120254389/2500000000 : ℝ), (16918367/40000000 : ℝ)] ![(3331737744349/10000000000000 : ℝ), (2163311103531/6250000000000 : ℝ), (32069644889081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353522219/10000000000 : ℝ)|^8415 ≤ (3331737744349/10000000000000 : ℝ)^6367
        have hw : |(4353522219/10000000000 : ℝ)|=(4353522219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120254389/2500000000 : ℝ)|^8415 ≤ (2163311103531/6250000000000 : ℝ)^6367
        have hw : |(1120254389/2500000000 : ℝ)|=(1120254389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16918367/40000000 : ℝ)|^8415 ≤ (32069644889081/100000000000000 : ℝ)^6367
        have hw : |(16918367/40000000 : ℝ)|=(16918367/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (229/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11427/100000 : ℝ) ^ (4207/1024 : ℝ) ≤ (2695505551519721/20000000000000000000 : ℝ) := by
    have hpowers : (11427/100000 : ℝ)^4207 ≤ (2695505551519721/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11427 : ℕ)^4207*20000000000000000000^1024 ≤ 2695505551519721^1024*100000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11427 100000 2695505551519721 20000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11427/100000 : ℝ)) (X := (2695505551519721/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7061/50000 : ℝ) ^ (4207/1024 : ℝ) ≤ (32168803344996751/100000000000000000000 : ℝ) := by
    have hpowers : (7061/50000 : ℝ)^4207 ≤ (32168803344996751/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7061 : ℕ)^4207*100000000000000000000^1024 ≤ 32168803344996751^1024*50000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7061 50000 32168803344996751 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7061/50000 : ℝ)) (X := (32168803344996751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002695505551519721/10000000000000000000 : ℝ) ≤ (2500164007384749/2500000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (10002695505551519721/10000000000000000000 : ℝ)^1024 ≤ (2500164007384749/2500000000000000 : ℝ)^4207 := by
      have hnat : (10002695505551519721 : ℕ)^1024*2500000000000000^4207 ≤ 2500164007384749^4207*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002695505551519721 10000000000000000000 2500164007384749 2500000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500164007384749/2500000000000000 : ℝ)) (X := (10002695505551519721/10000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011411582775648839/25000000000000000000 : ℝ) ≤ (2000222171494471/2000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25011411582775648839/25000000000000000000 : ℝ)^1024 ≤ (2000222171494471/2000000000000000 : ℝ)^4207 := by
      have hnat : (25011411582775648839 : ℕ)^1024*2000000000000000^4207 ≤ 2000222171494471^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011411582775648839 25000000000000000000 2000222171494471 2000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222171494471/2000000000000000 : ℝ)) (X := (25011411582775648839/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032168803344996751/50000000000000000000 : ℝ) ≤ (5000782842702857/5000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50032168803344996751/50000000000000000000 : ℝ)^1024 ≤ (5000782842702857/5000000000000000 : ℝ)^4207 := by
      have hnat : (50032168803344996751 : ℕ)^1024*5000000000000000^4207 ≤ 5000782842702857^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032168803344996751 50000000000000000000 5000782842702857 5000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000782842702857/5000000000000000 : ℝ)) (X := (50032168803344996751/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2695505551519721/20000000000000000000 : ℝ) ≤ ((13470686681009303817/13475000000000000000 : ℝ)+2*(454827933359/269500000000000 : ℝ)*(11427/100000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (13470686681009303817/13475000000000000000 : ℝ)+2*(454827933359/269500000000000 : ℝ)*(11427/100000 : ℝ)=(2500164007384749/2500000000000000 : ℝ) by norm_num, show 1+2*(2695505551519721/20000000000000000000 : ℝ)=(10002695505551519721/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32168803344996751/100000000000000000000 : ℝ)+(2695505551519721/20000000000000000000 : ℝ) ≤ ((13470686681009303817/13475000000000000000 : ℝ)+(454827933359/269500000000000 : ℝ)*((7061/50000 : ℝ)+(11427/100000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (13470686681009303817/13475000000000000000 : ℝ)+(454827933359/269500000000000 : ℝ)*((7061/50000 : ℝ)+(11427/100000 : ℝ))=(2000222171494471/2000000000000000 : ℝ) by norm_num, show 1+(32168803344996751/100000000000000000000 : ℝ)+(2695505551519721/20000000000000000000 : ℝ)=(25011411582775648839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32168803344996751/100000000000000000000 : ℝ) ≤ ((13470686681009303817/13475000000000000000 : ℝ)+2*(454827933359/269500000000000 : ℝ)*(7061/50000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (13470686681009303817/13475000000000000000 : ℝ)+2*(454827933359/269500000000000 : ℝ)*(7061/50000 : ℝ)=(5000782842702857/5000000000000000 : ℝ) by norm_num, show 1+2*(32168803344996751/100000000000000000000 : ℝ)=(50032168803344996751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13470686681009303817/13475000000000000000 : ℝ)*(X 1 0+X 2 0)+(454827933359/269500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (13470686681009303817/13475000000000000000 : ℝ)) (alpha := (454827933359/269500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13470686681009303817/13475000000000000000 : ℝ)*(X 0 1+X 2 1)+(454827933359/269500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (13470686681009303817/13475000000000000000 : ℝ)) (alpha := (454827933359/269500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13470686681009303817/13475000000000000000 : ℝ)*(X 0 2+X 1 2)+(454827933359/269500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (13470686681009303817/13475000000000000000 : ℝ)) (alpha := (454827933359/269500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064593533/5000000000 : ℝ)*X 0 0+(2695894869/5000000000 : ℝ)*X 0 1+(263336669/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672233471/5000000000 : ℝ)*X 1 0+(-2192601291/10000000000 : ℝ)*X 1 1+(1316683423/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068893411/2000000000 : ℝ)*X 2 0+(5266733481/10000000000 : ℝ)*X 2 1+(-109630071/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353512709/10000000000 : ℝ)*X 0 0+(4228950341/10000000000 : ℝ)*X 0 1+(4481656553/10000000000 : ℝ)*X 0 2+(4353512709/10000000000 : ℝ)*X 1 0+(4228950341/10000000000 : ℝ)*X 1 1+(4481656553/10000000000 : ℝ)*X 1 2+(4353512709/10000000000 : ℝ)*X 2 0+(4228950341/10000000000 : ℝ)*X 2 1+(4481656553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2129191759/10000000000 : ℝ)*X 0 0+(5267049687/10000000000 : ℝ)*X 0 1+(5391472323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664075241/1250000000 : ℝ)*X 1 0+(-516965619/2500000000 : ℝ)*X 1 1+(2695736189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265630093/500000000 : ℝ)*X 2 0+(168483513/312500000 : ℝ)*X 2 1+(-2067862517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353522219/10000000000 : ℝ)*X 0 0+(1120254389/2500000000 : ℝ)*X 0 1+(16918367/40000000 : ℝ)*X 0 2+(4353522219/10000000000 : ℝ)*X 1 0+(1120254389/2500000000 : ℝ)*X 1 1+(16918367/40000000 : ℝ)*X 1 2+(4353522219/10000000000 : ℝ)*X 2 0+(1120254389/2500000000 : ℝ)*X 2 1+(16918367/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134664399345340303282184907/67375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (312649811/100000000000000 : ℝ)*(base19) + (479711061/100000000000000 : ℝ)*(base23) + (1229209/625000000000 : ℝ)*(upper3) + (1074369/100000000000000 : ℝ)*(upper4) + (2998813/20000000000000 : ℝ)*(upper5) + (1195361627242257/20000000000000 : ℝ)*(major0) + (1195361627242257/20000000000000 : ℝ)*(major1) + (1195361627242257/20000000000000 : ℝ)*(major2) + (199910452215413/2500000000000 : ℝ)*(sp0) + (3998216936824511/50000000000000 : ℝ)*(sp1) + (7996433706587773/100000000000000 : ℝ)*(sp2) + (3957170851998601/100000000000000 : ℝ)*(sp3) + (16097682313/100000000000000 : ℝ)*(sp4) + (11167500813/100000000000000 : ℝ)*(sp7) + (1978591009749707/50000000000000 : ℝ)*(f.failure) + (7996434186298833/100000000000000 : ℝ)*(f.sum) + (3247617874673/673750000000000000000000000 : ℝ)*base66 + (2402770524583055031/269500000000000000000000000000000 : ℝ)*base68 + (488632440097944969/269500000000000000000000000000000 : ℝ)*base69 + (3309452371423055031/269500000000000000000000000000000 : ℝ)*base72 + (926642543401/1347500000000000000000000000 : ℝ)*base74 + (1198623117389555031/269500000000000000000000000000000 : ℝ)*base76 + (2305480731097555031/269500000000000000000000000000000 : ℝ)*base78 + (2149162945512055031/269500000000000000000000000000000 : ℝ)*base80 + (1421404671189/1347500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15832723/2500000000000000000000 : ℝ)*base89 + (15832723/2500000000000000000000 : ℝ)*base91 + (15832723/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (308565314950902365427/34375000000000000000000000 : ℝ) := by norm_num
    linear_combination (6497729/390625000000 : ℝ)*(base19) + (1675265831/100000000000000 : ℝ)*(base23) + (432251/200000000000 : ℝ)*(upper3) + (29487563/50000000000000 : ℝ)*(lower4) + (196716081/100000000000000 : ℝ)*(upper5) + (3003608738461821/50000000000000 : ℝ)*(major0) + (3003608738461821/50000000000000 : ℝ)*(major1) + (3003608738461821/50000000000000 : ℝ)*(major2) + (47673239269/100000000000000 : ℝ)*(sp1) + (24145790381/50000000000000 : ℝ)*(sp2) + (8037118929390861/100000000000000 : ℝ)*(sp4) + (1004633699091621/12500000000000 : ℝ)*(sp5) + (2009267240636067/25000000000000 : ℝ)*(sp6) + (994328931310391/25000000000000 : ℝ)*(sp7) + (994328931310391/25000000000000 : ℝ)*(f.failure) + (8037118929390861/100000000000000 : ℝ)*(f.sum) + (295696097053/275000000000000000000000000 : ℝ)*base66 + (110318981401423893/13750000000000000000000000000000 : ℝ)*base67 + (192435792513576107/13750000000000000000000000000000 : ℝ)*base70 + (37815407844826107/13750000000000000000000000000000 : ℝ)*base72 + (1749452359947/275000000000000000000000000 : ℝ)*base73 + (96062990562326107/13750000000000000000000000000000 : ℝ)*base76 + (57372725195173893/13750000000000000000000000000000 : ℝ)*base77 + (134916445735173893/13750000000000000000000000000000 : ℝ)*base79 + (204225301739/137500000000000000000000000 : ℝ)*base82 + (6680801/1250000000000000000000 : ℝ)*base90 + (6680801/1250000000000000000000 : ℝ)*base92 + (6680801/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1222_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1222_s7_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064601339/5000000000 : ℝ)*x 0 + (5391571377/10000000000 : ℝ)*x 1 + (2633470863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064601339/5000000000 : ℝ)^8415 ≤ (12945900296631/100000000000000 : ℝ)^6367 := by
    have hnat : (1064601339 : ℕ)^8415*100000000000000^6367 ≤ 12945900296631^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064601339 5000000000 12945900296631 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391571377/10000000000 : ℝ)^8415 ≤ (44199698809103/100000000000000 : ℝ)^6367 := by
    have hnat : (5391571377 : ℕ)^8415*100000000000000^6367 ≤ 44199698809103^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391571377 10000000000 44199698809103 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633470863/5000000000 : ℝ)^8415 ≤ (21427200440741/50000000000000 : ℝ)^6367 := by
    have hnat : (2633470863 : ℕ)^8415*50000000000000^6367 ≤ 21427200440741^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633470863 5000000000 21427200440741 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064601339/5000000000 : ℝ), (5391571377/10000000000 : ℝ), (2633470863/5000000000 : ℝ)] ![(12945900296631/100000000000000 : ℝ), (44199698809103/100000000000000 : ℝ), (21427200440741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064601339/5000000000 : ℝ)|^8415 ≤ (12945900296631/100000000000000 : ℝ)^6367
        have hw : |(-1064601339/5000000000 : ℝ)|=(1064601339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391571377/10000000000 : ℝ)|^8415 ≤ (44199698809103/100000000000000 : ℝ)^6367
        have hw : |(5391571377/10000000000 : ℝ)|=(5391571377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633470863/5000000000 : ℝ)|^8415 ≤ (21427200440741/50000000000000 : ℝ)^6367
        have hw : |(2633470863/5000000000 : ℝ)|=(2633470863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s7_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344412821/10000000000 : ℝ)*x 0 + (-2192397241/10000000000 : ℝ)*x 1 + (2633470997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344412821/10000000000 : ℝ)^8415 ≤ (4368946275783/10000000000000 : ℝ)^6367 := by
    have hnat : (5344412821 : ℕ)^8415*10000000000000^6367 ≤ 4368946275783^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344412821 10000000000 4368946275783 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192397241/10000000000 : ℝ)^8415 ≤ (2691226694163/20000000000000 : ℝ)^6367 := by
    have hnat : (2192397241 : ℕ)^8415*20000000000000^6367 ≤ 2691226694163^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192397241 10000000000 2691226694163 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633470997/5000000000 : ℝ)^8415 ≤ (21427201881731/50000000000000 : ℝ)^6367 := by
    have hnat : (2633470997 : ℕ)^8415*50000000000000^6367 ≤ 21427201881731^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633470997 5000000000 21427201881731 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344412821/10000000000 : ℝ), (-2192397241/10000000000 : ℝ), (2633470997/5000000000 : ℝ)] ![(4368946275783/10000000000000 : ℝ), (2691226694163/20000000000000 : ℝ), (21427201881731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344412821/10000000000 : ℝ)|^8415 ≤ (4368946275783/10000000000000 : ℝ)^6367
        have hw : |(5344412821/10000000000 : ℝ)|=(5344412821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192397241/10000000000 : ℝ)|^8415 ≤ (2691226694163/20000000000000 : ℝ)^6367
        have hw : |(-2192397241/10000000000 : ℝ)|=(2192397241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633470997/5000000000 : ℝ)|^8415 ≤ (21427201881731/50000000000000 : ℝ)^6367
        have hw : |(2633470997/5000000000 : ℝ)|=(2633470997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s7_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336103173/2500000000 : ℝ)*x 0 + (658367717/1250000000 : ℝ)*x 1 + (-1096198877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336103173/2500000000 : ℝ)^8415 ≤ (21844730682039/50000000000000 : ℝ)^6367 := by
    have hnat : (1336103173 : ℕ)^8415*50000000000000^6367 ≤ 21844730682039^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336103173 2500000000 21844730682039 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658367717/1250000000 : ℝ)^8415 ≤ (21427200494509/50000000000000 : ℝ)^6367 := by
    have hnat : (658367717 : ℕ)^8415*50000000000000^6367 ≤ 21427200494509^6367*1250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658367717 1250000000 21427200494509 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096198877/5000000000 : ℝ)^8415 ≤ (6728068816099/50000000000000 : ℝ)^6367 := by
    have hnat : (1096198877 : ℕ)^8415*50000000000000^6367 ≤ 6728068816099^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096198877 5000000000 6728068816099 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336103173/2500000000 : ℝ), (658367717/1250000000 : ℝ), (-1096198877/5000000000 : ℝ)] ![(21844730682039/50000000000000 : ℝ), (21427200494509/50000000000000 : ℝ), (6728068816099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336103173/2500000000 : ℝ)|^8415 ≤ (21844730682039/50000000000000 : ℝ)^6367
        have hw : |(1336103173/2500000000 : ℝ)|=(1336103173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658367717/1250000000 : ℝ)|^8415 ≤ (21427200494509/50000000000000 : ℝ)^6367
        have hw : |(658367717/1250000000 : ℝ)|=(658367717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1096198877/5000000000 : ℝ)|^8415 ≤ (6728068816099/50000000000000 : ℝ)^6367
        have hw : |(-1096198877/5000000000 : ℝ)|=(1096198877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s7_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353523239/10000000000 : ℝ)*x 0 + (1057345051/2500000000 : ℝ)*x 1 + (2240612097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353523239/10000000000 : ℝ)^8415 ≤ (33317387760397/100000000000000 : ℝ)^6367 := by
    have hnat : (4353523239 : ℕ)^8415*100000000000000^6367 ≤ 33317387760397^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353523239 10000000000 33317387760397 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057345051/2500000000 : ℝ)^8415 ≤ (32067524984587/100000000000000 : ℝ)^6367 := by
    have hnat : (1057345051 : ℕ)^8415*100000000000000^6367 ≤ 32067524984587^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057345051 2500000000 32067524984587 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240612097/5000000000 : ℝ)^8415 ≤ (3461508723163/10000000000000 : ℝ)^6367 := by
    have hnat : (2240612097 : ℕ)^8415*10000000000000^6367 ≤ 3461508723163^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240612097 5000000000 3461508723163 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353523239/10000000000 : ℝ), (1057345051/2500000000 : ℝ), (2240612097/5000000000 : ℝ)] ![(33317387760397/100000000000000 : ℝ), (32067524984587/100000000000000 : ℝ), (3461508723163/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353523239/10000000000 : ℝ)|^8415 ≤ (33317387760397/100000000000000 : ℝ)^6367
        have hw : |(4353523239/10000000000 : ℝ)|=(4353523239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057345051/2500000000 : ℝ)|^8415 ≤ (32067524984587/100000000000000 : ℝ)^6367
        have hw : |(1057345051/2500000000 : ℝ)|=(1057345051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240612097/5000000000 : ℝ)|^8415 ≤ (3461508723163/10000000000000 : ℝ)^6367
        have hw : |(2240612097/5000000000 : ℝ)|=(2240612097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s7_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064603641/5000000000 : ℝ)*x 0 + (526725587/1000000000 : ℝ)*x 1 + (5391256167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064603641/5000000000 : ℝ)^8415 ≤ (1618242161741/12500000000000 : ℝ)^6367 := by
    have hnat : (1064603641 : ℕ)^8415*12500000000000^6367 ≤ 1618242161741^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064603641 5000000000 1618242161741 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526725587/1000000000 : ℝ)^8415 ≤ (171431116443/400000000000 : ℝ)^6367 := by
    have hnat : (526725587 : ℕ)^8415*400000000000^6367 ≤ 171431116443^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526725587 1000000000 171431116443 400000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391256167/10000000000 : ℝ)^8415 ≤ (22098141792823/50000000000000 : ℝ)^6367 := by
    have hnat : (5391256167 : ℕ)^8415*50000000000000^6367 ≤ 22098141792823^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391256167 10000000000 22098141792823 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064603641/5000000000 : ℝ), (526725587/1000000000 : ℝ), (5391256167/10000000000 : ℝ)] ![(1618242161741/12500000000000 : ℝ), (171431116443/400000000000 : ℝ), (22098141792823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064603641/5000000000 : ℝ)|^8415 ≤ (1618242161741/12500000000000 : ℝ)^6367
        have hw : |(-1064603641/5000000000 : ℝ)|=(1064603641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526725587/1000000000 : ℝ)|^8415 ≤ (171431116443/400000000000 : ℝ)^6367
        have hw : |(526725587/1000000000 : ℝ)|=(526725587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391256167/10000000000 : ℝ)|^8415 ≤ (22098141792823/50000000000000 : ℝ)^6367
        have hw : |(5391256167/10000000000 : ℝ)|=(5391256167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s7_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312656173/10000000000 : ℝ)*x 0 + (-2068083287/10000000000 : ℝ)*x 1 + (5391256149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312656173/10000000000 : ℝ)^8415 ≤ (43346683258267/100000000000000 : ℝ)^6367 := by
    have hnat : (5312656173 : ℕ)^8415*100000000000000^6367 ≤ 43346683258267^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312656173 10000000000 43346683258267 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068083287/10000000000 : ℝ)^8415 ≤ (622851667207/5000000000000 : ℝ)^6367 := by
    have hnat : (2068083287 : ℕ)^8415*5000000000000^6367 ≤ 622851667207^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068083287 10000000000 622851667207 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391256149/10000000000 : ℝ)^8415 ≤ (22098141695311/50000000000000 : ℝ)^6367 := by
    have hnat : (5391256149 : ℕ)^8415*50000000000000^6367 ≤ 22098141695311^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391256149 10000000000 22098141695311 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312656173/10000000000 : ℝ), (-2068083287/10000000000 : ℝ), (5391256149/10000000000 : ℝ)] ![(43346683258267/100000000000000 : ℝ), (622851667207/5000000000000 : ℝ), (22098141695311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312656173/10000000000 : ℝ)|^8415 ≤ (43346683258267/100000000000000 : ℝ)^6367
        have hw : |(5312656173/10000000000 : ℝ)|=(5312656173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068083287/10000000000 : ℝ)|^8415 ≤ (622851667207/5000000000000 : ℝ)^6367
        have hw : |(-2068083287/10000000000 : ℝ)|=(2068083287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391256149/10000000000 : ℝ)|^8415 ≤ (22098141695311/50000000000000 : ℝ)^6367
        have hw : |(5391256149/10000000000 : ℝ)|=(5391256149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s7_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33204101/62500000 : ℝ)*x 0 + (2695628087/5000000000 : ℝ)*x 1 + (-206808327/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33204101/62500000 : ℝ)^8415 ≤ (16932298093/39062500000 : ℝ)^6367 := by
    have hnat : (33204101 : ℕ)^8415*39062500000^6367 ≤ 16932298093^6367*62500000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33204101 62500000 16932298093 39062500000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695628087/5000000000 : ℝ)^8415 ≤ (2762267728843/6250000000000 : ℝ)^6367 := by
    have hnat : (2695628087 : ℕ)^8415*6250000000000^6367 ≤ 2762267728843^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695628087 5000000000 2762267728843 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206808327/1000000000 : ℝ)^8415 ≤ (3114258302201/25000000000000 : ℝ)^6367 := by
    have hnat : (206808327 : ℕ)^8415*25000000000000^6367 ≤ 3114258302201^6367*1000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206808327 1000000000 3114258302201 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33204101/62500000 : ℝ), (2695628087/5000000000 : ℝ), (-206808327/1000000000 : ℝ)] ![(16932298093/39062500000 : ℝ), (2762267728843/6250000000000 : ℝ), (3114258302201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33204101/62500000 : ℝ)|^8415 ≤ (16932298093/39062500000 : ℝ)^6367
        have hw : |(33204101/62500000 : ℝ)|=(33204101/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695628087/5000000000 : ℝ)|^8415 ≤ (2762267728843/6250000000000 : ℝ)^6367
        have hw : |(2695628087/5000000000 : ℝ)|=(2695628087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206808327/1000000000 : ℝ)|^8415 ≤ (3114258302201/25000000000000 : ℝ)^6367
        have hw : |(-206808327/1000000000 : ℝ)|=(206808327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s7_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353532869/10000000000 : ℝ)*x 0 + (1120147351/2500000000 : ℝ)*x 1 + (2115008583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353532869/10000000000 : ℝ)^8415 ≤ (8329371291043/25000000000000 : ℝ)^6367 := by
    have hnat : (4353532869 : ℕ)^8415*25000000000000^6367 ≤ 8329371291043^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353532869 10000000000 8329371291043 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120147351/2500000000 : ℝ)^8415 ≤ (3460860673617/10000000000000 : ℝ)^6367 := by
    have hnat : (1120147351 : ℕ)^8415*10000000000000^6367 ≤ 3460860673617^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120147351 2500000000 3460860673617 10000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115008583/5000000000 : ℝ)^8415 ≤ (32073908090149/100000000000000 : ℝ)^6367 := by
    have hnat : (2115008583 : ℕ)^8415*100000000000000^6367 ≤ 32073908090149^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115008583 5000000000 32073908090149 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353532869/10000000000 : ℝ), (1120147351/2500000000 : ℝ), (2115008583/5000000000 : ℝ)] ![(8329371291043/25000000000000 : ℝ), (3460860673617/10000000000000 : ℝ), (32073908090149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353532869/10000000000 : ℝ)|^8415 ≤ (8329371291043/25000000000000 : ℝ)^6367
        have hw : |(4353532869/10000000000 : ℝ)|=(4353532869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120147351/2500000000 : ℝ)|^8415 ≤ (3460860673617/10000000000000 : ℝ)^6367
        have hw : |(1120147351/2500000000 : ℝ)|=(1120147351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115008583/5000000000 : ℝ)|^8415 ≤ (32073908090149/100000000000000 : ℝ)^6367
        have hw : |(2115008583/5000000000 : ℝ)|=(2115008583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (5727/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (229/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (229/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (229/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (229/2000 : ℝ) ^ (4207/1024 : ℝ) ≤ (13589326464302807/100000000000000000000 : ℝ) := by
    have hpowers : (229/2000 : ℝ)^4207 ≤ (13589326464302807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (229 : ℕ)^4207*100000000000000000000^1024 ≤ 13589326464302807^1024*2000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        229 2000 13589326464302807 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (229/2000 : ℝ)) (X := (13589326464302807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14099/100000 : ℝ) ^ (4207/1024 : ℝ) ≤ (31954099589459109/100000000000000000000 : ℝ) := by
    have hpowers : (14099/100000 : ℝ)^4207 ≤ (31954099589459109/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14099 : ℕ)^4207*100000000000000000000^1024 ≤ 31954099589459109^1024*100000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14099 100000 31954099589459109 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14099/100000 : ℝ)) (X := (31954099589459109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013589326464302807/50000000000000000000 : ℝ) ≤ (10000661470871863/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50013589326464302807/50000000000000000000 : ℝ)^1024 ≤ (10000661470871863/10000000000000000 : ℝ)^4207 := by
      have hnat : (50013589326464302807 : ℕ)^1024*10000000000000000^4207 ≤ 10000661470871863^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013589326464302807 50000000000000000000 10000661470871863 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000661470871863/10000000000000000 : ℝ)) (X := (50013589326464302807/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011385856513440479/25000000000000000000 : ℝ) ≤ (2500277088396889/2500000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25011385856513440479/25000000000000000000 : ℝ)^1024 ≤ (2500277088396889/2500000000000000 : ℝ)^4207 := by
      have hnat : (25011385856513440479 : ℕ)^1024*2500000000000000^4207 ≤ 2500277088396889^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011385856513440479 25000000000000000000 2500277088396889 2500000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500277088396889/2500000000000000 : ℝ)) (X := (25011385856513440479/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031954099589459109/50000000000000000000 : ℝ) ≤ (10001555236303249/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50031954099589459109/50000000000000000000 : ℝ)^1024 ≤ (10001555236303249/10000000000000000 : ℝ)^4207 := by
      have hnat : (50031954099589459109 : ℕ)^1024*10000000000000000^4207 ≤ 10001555236303249^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031954099589459109 50000000000000000000 10001555236303249 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001555236303249/10000000000000000 : ℝ)) (X := (50031954099589459109/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13589326464302807/100000000000000000000 : ℝ) ≤ ((8827172874050065129/8830000000000000000 : ℝ)+2*(148960905231/88300000000000 : ℝ)*(229/2000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (8827172874050065129/8830000000000000000 : ℝ)+2*(148960905231/88300000000000 : ℝ)*(229/2000 : ℝ)=(10000661470871863/10000000000000000 : ℝ) by norm_num, show 1+2*(13589326464302807/100000000000000000000 : ℝ)=(50013589326464302807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31954099589459109/100000000000000000000 : ℝ)+(13589326464302807/100000000000000000000 : ℝ) ≤ ((8827172874050065129/8830000000000000000 : ℝ)+(148960905231/88300000000000 : ℝ)*((14099/100000 : ℝ)+(229/2000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (8827172874050065129/8830000000000000000 : ℝ)+(148960905231/88300000000000 : ℝ)*((14099/100000 : ℝ)+(229/2000 : ℝ))=(2500277088396889/2500000000000000 : ℝ) by norm_num, show 1+(31954099589459109/100000000000000000000 : ℝ)+(13589326464302807/100000000000000000000 : ℝ)=(25011385856513440479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31954099589459109/100000000000000000000 : ℝ) ≤ ((8827172874050065129/8830000000000000000 : ℝ)+2*(148960905231/88300000000000 : ℝ)*(14099/100000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (8827172874050065129/8830000000000000000 : ℝ)+2*(148960905231/88300000000000 : ℝ)*(14099/100000 : ℝ)=(10001555236303249/10000000000000000 : ℝ) by norm_num, show 1+2*(31954099589459109/100000000000000000000 : ℝ)=(50031954099589459109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8827172874050065129/8830000000000000000 : ℝ)*(X 1 0+X 2 0)+(148960905231/88300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (8827172874050065129/8830000000000000000 : ℝ)) (alpha := (148960905231/88300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8827172874050065129/8830000000000000000 : ℝ)*(X 0 1+X 2 1)+(148960905231/88300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (8827172874050065129/8830000000000000000 : ℝ)) (alpha := (148960905231/88300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8827172874050065129/8830000000000000000 : ℝ)*(X 0 2+X 1 2)+(148960905231/88300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (229/2000 : ℝ)) (hi := (14099/100000 : ℝ)) (c := (8827172874050065129/8830000000000000000 : ℝ)) (alpha := (148960905231/88300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064601339/5000000000 : ℝ)*X 0 0+(5391571377/10000000000 : ℝ)*X 0 1+(2633470863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344412821/10000000000 : ℝ)*X 1 0+(-2192397241/10000000000 : ℝ)*X 1 1+(2633470997/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336103173/2500000000 : ℝ)*X 2 0+(658367717/1250000000 : ℝ)*X 2 1+(-1096198877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353523239/10000000000 : ℝ)*X 0 0+(1057345051/2500000000 : ℝ)*X 0 1+(2240612097/5000000000 : ℝ)*X 0 2+(4353523239/10000000000 : ℝ)*X 1 0+(1057345051/2500000000 : ℝ)*X 1 1+(2240612097/5000000000 : ℝ)*X 1 2+(4353523239/10000000000 : ℝ)*X 2 0+(1057345051/2500000000 : ℝ)*X 2 1+(2240612097/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064603641/5000000000 : ℝ)*X 0 0+(526725587/1000000000 : ℝ)*X 0 1+(5391256167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312656173/10000000000 : ℝ)*X 1 0+(-2068083287/10000000000 : ℝ)*X 1 1+(5391256149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33204101/62500000 : ℝ)*X 2 0+(2695628087/5000000000 : ℝ)*X 2 1+(-206808327/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353532869/10000000000 : ℝ)*X 0 0+(1120147351/2500000000 : ℝ)*X 0 1+(2115008583/5000000000 : ℝ)*X 0 2+(4353532869/10000000000 : ℝ)*X 1 0+(1120147351/2500000000 : ℝ)*X 1 1+(2115008583/5000000000 : ℝ)*X 1 2+(4353532869/10000000000 : ℝ)*X 2 0+(1120147351/2500000000 : ℝ)*X 2 1+(2115008583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (484678018816108058985927273/88300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1393607573/100000000000000 : ℝ)*(base19) + (153821383/12500000000000 : ℝ)*(base23) + (84662763/100000000000000 : ℝ)*(upper2) + (60781263/25000000000000 : ℝ)*(upper3) + (1199466266319179/20000000000000 : ℝ)*(major0) + (1199466266319179/20000000000000 : ℝ)*(major1) + (1199466266319179/20000000000000 : ℝ)*(major2) + (8023841468144911/100000000000000 : ℝ)*(sp0) + (16047781749147/200000000000 : ℝ)*(sp1) + (8023869533999247/100000000000000 : ℝ)*(sp2) + (496342483749293/12500000000000 : ℝ)*(sp3) + (25400018081/50000000000000 : ℝ)*(sp4) + (10751805381/50000000000000 : ℝ)*(sp6) + (948189061/3125000000000 : ℝ)*(sp7) + (1985385106022147/50000000000000 : ℝ)*(f.failure) + (8023892268181073/100000000000000 : ℝ)*(f.sum) + (6044983224697/883000000000000000000000000 : ℝ)*base66 + (1672145436411890909/176600000000000000000000000000000 : ℝ)*base68 + (1509999093346090909/176600000000000000000000000000000 : ℝ)*base70 + (1377526805719690909/176600000000000000000000000000000 : ℝ)*base72 + (4399364488423/883000000000000000000000000 : ℝ)*base74 + (216514637157909091/176600000000000000000000000000000 : ℝ)*base75 + (59998369729909091/176600000000000000000000000000000 : ℝ)*base77 + (1495480799575690909/176600000000000000000000000000000 : ℝ)*base80 + (953042425221/883000000000000000000000000 : ℝ)*base82 + (33024117/2500000000000000000000 : ℝ)*base90 + (33024117/2500000000000000000000 : ℝ)*base92 + (33024117/2500000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14042868582603817611/2759375000000000000000000 : ℝ) := by norm_num
    linear_combination (858922589/100000000000000 : ℝ)*(base19) + (465947389/50000000000000 : ℝ)*(base23) + (43184279/50000000000000 : ℝ)*(upper3) + (42175777/100000000000000 : ℝ)*(lower4) + (22480367/20000000000000 : ℝ)*(upper5) + (1205536108445881/20000000000000 : ℝ)*(major0) + (1205536108445881/20000000000000 : ℝ)*(major1) + (1205536108445881/20000000000000 : ℝ)*(major2) + (2372785021/10000000000000 : ℝ)*(sp1) + (6489010113/25000000000000 : ℝ)*(sp2) + (1612899361705803/20000000000000 : ℝ)*(sp4) + (1008059027719527/12500000000000 : ℝ)*(sp5) + (1612893984118757/20000000000000 : ℝ)*(sp6) + (399086410629151/10000000000000 : ℝ)*(sp7) + (399086410629151/10000000000000 : ℝ)*(f.failure) + (1612899361705803/20000000000000 : ℝ)*(f.sum) + (5517997873831/883000000000000000000000000 : ℝ)*base65 + (35076735321116351/176600000000000000000000000000000 : ℝ)*base68 + (1046648052633883649/176600000000000000000000000000000 : ℝ)*base69 + (3220601151424083649/176600000000000000000000000000000 : ℝ)*base71 + (181523375757/883000000000000000000000000 : ℝ)*base73 + (4103450404361516351/176600000000000000000000000000000 : ℝ)*base76 + (474980005604483649/176600000000000000000000000000000 : ℝ)*base77 + (166876001760316351/176600000000000000000000000000000 : ℝ)*base80 + (937015630609/176600000000000000000000000 : ℝ)*base81 + (2127161/500000000000000000000 : ℝ)*base90 + (2127161/500000000000000000000 : ℝ)*base92 + (2127161/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1222_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (229/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1222_s8_0 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129208647/10000000000 : ℝ)*x 0 + (5391527537/10000000000 : ℝ)*x 1 + (1316745359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129208647/10000000000 : ℝ)^8415 ≤ (647297413147/5000000000000 : ℝ)^6367 := by
    have hnat : (2129208647 : ℕ)^8415*5000000000000^6367 ≤ 647297413147^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129208647 10000000000 647297413147 5000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391527537/10000000000 : ℝ)^8415 ≤ (2762451488097/6250000000000 : ℝ)^6367 := by
    have hnat : (5391527537 : ℕ)^8415*6250000000000^6367 ≤ 2762451488097^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391527537 10000000000 2762451488097 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316745359/2500000000 : ℝ)^8415 ≤ (10713706977431/25000000000000 : ℝ)^6367 := by
    have hnat : (1316745359 : ℕ)^8415*25000000000000^6367 ≤ 10713706977431^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316745359 2500000000 10713706977431 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129208647/10000000000 : ℝ), (5391527537/10000000000 : ℝ), (1316745359/2500000000 : ℝ)] ![(647297413147/5000000000000 : ℝ), (2762451488097/6250000000000 : ℝ), (10713706977431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129208647/10000000000 : ℝ)|^8415 ≤ (647297413147/5000000000000 : ℝ)^6367
        have hw : |(-2129208647/10000000000 : ℝ)|=(2129208647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391527537/10000000000 : ℝ)|^8415 ≤ (2762451488097/6250000000000 : ℝ)^6367
        have hw : |(5391527537/10000000000 : ℝ)|=(5391527537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316745359/2500000000 : ℝ)|^8415 ≤ (10713706977431/25000000000000 : ℝ)^6367
        have hw : |(1316745359/2500000000 : ℝ)|=(1316745359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s8_1 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213776037/400000000 : ℝ)*x 0 + (-2192360797/10000000000 : ℝ)*x 1 + (1316745359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213776037/400000000 : ℝ)^8415 ≤ (21844667115059/50000000000000 : ℝ)^6367 := by
    have hnat : (213776037 : ℕ)^8415*50000000000000^6367 ≤ 21844667115059^6367*400000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213776037 400000000 21844667115059 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192360797/10000000000 : ℝ)^8415 ≤ (13455837843073/100000000000000 : ℝ)^6367 := by
    have hnat : (2192360797 : ℕ)^8415*100000000000000^6367 ≤ 13455837843073^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192360797 10000000000 13455837843073 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316745359/2500000000 : ℝ)^8415 ≤ (10713706977431/25000000000000 : ℝ)^6367 := by
    have hnat : (1316745359 : ℕ)^8415*25000000000000^6367 ≤ 10713706977431^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316745359 2500000000 10713706977431 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213776037/400000000 : ℝ), (-2192360797/10000000000 : ℝ), (1316745359/2500000000 : ℝ)] ![(21844667115059/50000000000000 : ℝ), (13455837843073/100000000000000 : ℝ), (10713706977431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213776037/400000000 : ℝ)|^8415 ≤ (21844667115059/50000000000000 : ℝ)^6367
        have hw : |(213776037/400000000 : ℝ)|=(213776037/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192360797/10000000000 : ℝ)|^8415 ≤ (13455837843073/100000000000000 : ℝ)^6367
        have hw : |(-2192360797/10000000000 : ℝ)|=(2192360797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316745359/2500000000 : ℝ)|^8415 ≤ (10713706977431/25000000000000 : ℝ)^6367
        have hw : |(1316745359/2500000000 : ℝ)|=(1316745359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s8_2 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344400953/10000000000 : ℝ)*x 0 + (5266981409/10000000000 : ℝ)*x 1 + (-548090199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344400953/10000000000 : ℝ)^8415 ≤ (43689334532637/100000000000000 : ℝ)^6367 := by
    have hnat : (5344400953 : ℕ)^8415*100000000000000^6367 ≤ 43689334532637^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344400953 10000000000 43689334532637 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266981409/10000000000 : ℝ)^8415 ≤ (68567724191/160000000000 : ℝ)^6367 := by
    have hnat : (5266981409 : ℕ)^8415*160000000000^6367 ≤ 68567724191^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266981409 10000000000 68567724191 160000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548090199/2500000000 : ℝ)^8415 ≤ (13455837834961/100000000000000 : ℝ)^6367 := by
    have hnat : (548090199 : ℕ)^8415*100000000000000^6367 ≤ 13455837834961^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548090199 2500000000 13455837834961 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344400953/10000000000 : ℝ), (5266981409/10000000000 : ℝ), (-548090199/2500000000 : ℝ)] ![(43689334532637/100000000000000 : ℝ), (68567724191/160000000000 : ℝ), (13455837834961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344400953/10000000000 : ℝ)|^8415 ≤ (43689334532637/100000000000000 : ℝ)^6367
        have hw : |(5344400953/10000000000 : ℝ)|=(5344400953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266981409/10000000000 : ℝ)|^8415 ≤ (68567724191/160000000000 : ℝ)^6367
        have hw : |(5266981409/10000000000 : ℝ)|=(5266981409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548090199/2500000000 : ℝ)|^8415 ≤ (13455837834961/100000000000000 : ℝ)^6367
        have hw : |(-548090199/2500000000 : ℝ)|=(548090199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s8_3 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353525433/10000000000 : ℝ)*x 0 + (4229464291/10000000000 : ℝ)*x 1 + (1120284871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353525433/10000000000 : ℝ)^8415 ≤ (33317409951863/100000000000000 : ℝ)^6367 := by
    have hnat : (4353525433 : ℕ)^8415*100000000000000^6367 ≤ 33317409951863^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353525433 10000000000 33317409951863 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229464291/10000000000 : ℝ)^8415 ≤ (2004272976071/6250000000000 : ℝ)^6367 := by
    have hnat : (4229464291 : ℕ)^8415*6250000000000^6367 ≤ 2004272976071^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229464291 10000000000 2004272976071 6250000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120284871/2500000000 : ℝ)^8415 ≤ (34614222420261/100000000000000 : ℝ)^6367 := by
    have hnat : (1120284871 : ℕ)^8415*100000000000000^6367 ≤ 34614222420261^6367*2500000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120284871 2500000000 34614222420261 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353525433/10000000000 : ℝ), (4229464291/10000000000 : ℝ), (1120284871/2500000000 : ℝ)] ![(33317409951863/100000000000000 : ℝ), (2004272976071/6250000000000 : ℝ), (34614222420261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353525433/10000000000 : ℝ)|^8415 ≤ (33317409951863/100000000000000 : ℝ)^6367
        have hw : |(4353525433/10000000000 : ℝ)|=(4353525433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229464291/10000000000 : ℝ)|^8415 ≤ (2004272976071/6250000000000 : ℝ)^6367
        have hw : |(4229464291/10000000000 : ℝ)|=(4229464291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120284871/2500000000 : ℝ)|^8415 ≤ (34614222420261/100000000000000 : ℝ)^6367
        have hw : |(1120284871/2500000000 : ℝ)|=(1120284871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s8_4 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064606733/5000000000 : ℝ)*x 0 + (1053459073/2000000000 : ℝ)*x 1 + (5391212379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064606733/5000000000 : ℝ)^8415 ≤ (1618248373499/12500000000000 : ℝ)^6367 := by
    have hnat : (1064606733 : ℕ)^8415*12500000000000^6367 ≤ 1618248373499^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064606733 5000000000 1618248373499 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053459073/2000000000 : ℝ)^8415 ≤ (42858203835099/100000000000000 : ℝ)^6367 := by
    have hnat : (1053459073 : ℕ)^8415*100000000000000^6367 ≤ 42858203835099^6367*2000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053459073 2000000000 42858203835099 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391212379/10000000000 : ℝ)^8415 ≤ (11048952289607/25000000000000 : ℝ)^6367 := by
    have hnat : (5391212379 : ℕ)^8415*25000000000000^6367 ≤ 11048952289607^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391212379 10000000000 11048952289607 25000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064606733/5000000000 : ℝ), (1053459073/2000000000 : ℝ), (5391212379/10000000000 : ℝ)] ![(1618248373499/12500000000000 : ℝ), (42858203835099/100000000000000 : ℝ), (11048952289607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064606733/5000000000 : ℝ)|^8415 ≤ (1618248373499/12500000000000 : ℝ)^6367
        have hw : |(-1064606733/5000000000 : ℝ)|=(1064606733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053459073/2000000000 : ℝ)|^8415 ≤ (42858203835099/100000000000000 : ℝ)^6367
        have hw : |(1053459073/2000000000 : ℝ)|=(1053459073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391212379/10000000000 : ℝ)|^8415 ≤ (11048952289607/25000000000000 : ℝ)^6367
        have hw : |(5391212379/10000000000 : ℝ)|=(5391212379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s8_5 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312665581/10000000000 : ℝ)*x 0 + (-1034064621/5000000000 : ℝ)*x 1 + (2695606509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312665581/10000000000 : ℝ)^8415 ≤ (21673392355163/50000000000000 : ℝ)^6367 := by
    have hnat : (5312665581 : ℕ)^8415*50000000000000^6367 ≤ 21673392355163^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312665581 10000000000 21673392355163 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034064621/5000000000 : ℝ)^8415 ≤ (12457399191727/100000000000000 : ℝ)^6367 := by
    have hnat : (1034064621 : ℕ)^8415*100000000000000^6367 ≤ 12457399191727^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034064621 5000000000 12457399191727 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695606509/5000000000 : ℝ)^8415 ≤ (22097908040877/50000000000000 : ℝ)^6367 := by
    have hnat : (2695606509 : ℕ)^8415*50000000000000^6367 ≤ 22097908040877^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695606509 5000000000 22097908040877 50000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312665581/10000000000 : ℝ), (-1034064621/5000000000 : ℝ), (2695606509/5000000000 : ℝ)] ![(21673392355163/50000000000000 : ℝ), (12457399191727/100000000000000 : ℝ), (22097908040877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312665581/10000000000 : ℝ)|^8415 ≤ (21673392355163/50000000000000 : ℝ)^6367
        have hw : |(5312665581/10000000000 : ℝ)|=(5312665581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034064621/5000000000 : ℝ)|^8415 ≤ (12457399191727/100000000000000 : ℝ)^6367
        have hw : |(-1034064621/5000000000 : ℝ)|=(1034064621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695606509/5000000000 : ℝ)|^8415 ≤ (22097908040877/50000000000000 : ℝ)^6367
        have hw : |(2695606509/5000000000 : ℝ)|=(2695606509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s8_6 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312665933/10000000000 : ℝ)*x 0 + (5391212479/10000000000 : ℝ)*x 1 + (-4136259/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312665933/10000000000 : ℝ)^8415 ≤ (43346788506153/100000000000000 : ℝ)^6367 := by
    have hnat : (5312665933 : ℕ)^8415*100000000000000^6367 ≤ 43346788506153^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312665933 10000000000 43346788506153 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391212479/10000000000 : ℝ)^8415 ≤ (44195810241891/100000000000000 : ℝ)^6367 := by
    have hnat : (5391212479 : ℕ)^8415*100000000000000^6367 ≤ 44195810241891^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391212479 10000000000 44195810241891 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4136259/20000000 : ℝ)^8415 ≤ (1557175155709/12500000000000 : ℝ)^6367 := by
    have hnat : (4136259 : ℕ)^8415*12500000000000^6367 ≤ 1557175155709^6367*20000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136259 20000000 1557175155709 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312665933/10000000000 : ℝ), (5391212479/10000000000 : ℝ), (-4136259/20000000 : ℝ)] ![(43346788506153/100000000000000 : ℝ), (44195810241891/100000000000000 : ℝ), (1557175155709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312665933/10000000000 : ℝ)|^8415 ≤ (43346788506153/100000000000000 : ℝ)^6367
        have hw : |(5312665933/10000000000 : ℝ)|=(5312665933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391212479/10000000000 : ℝ)|^8415 ≤ (44195810241891/100000000000000 : ℝ)^6367
        have hw : |(5391212479/10000000000 : ℝ)|=(5391212479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4136259/20000000 : ℝ)|^8415 ≤ (1557175155709/12500000000000 : ℝ)^6367
        have hw : |(-4136259/20000000 : ℝ)|=(4136259/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1222_s8_7 (p : ℝ) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108838371/250000000 : ℝ)*x 0 + (2240252953/5000000000 : ℝ)*x 1 + (4230100233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108838371/250000000 : ℝ)^8415 ≤ (33317505100093/100000000000000 : ℝ)^6367 := by
    have hnat : (108838371 : ℕ)^8415*100000000000000^6367 ≤ 33317505100093^6367*250000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108838371 250000000 33317505100093 100000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240252953/5000000000 : ℝ)^8415 ≤ (6921550867403/20000000000000 : ℝ)^6367 := by
    have hnat : (2240252953 : ℕ)^8415*20000000000000^6367 ≤ 6921550867403^6367*5000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240252953 5000000000 6921550867403 20000000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230100233/10000000000 : ℝ)^8415 ≤ (4009342567701/12500000000000 : ℝ)^6367 := by
    have hnat : (4230100233 : ℕ)^8415*12500000000000^6367 ≤ 4009342567701^6367*10000000000^8415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230100233 10000000000 4009342567701 12500000000000 8415 6367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8415/2048 : ℝ)) 8415 6367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108838371/250000000 : ℝ), (2240252953/5000000000 : ℝ), (4230100233/10000000000 : ℝ)] ![(33317505100093/100000000000000 : ℝ), (6921550867403/20000000000000 : ℝ), (4009342567701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108838371/250000000 : ℝ)|^8415 ≤ (33317505100093/100000000000000 : ℝ)^6367
        have hw : |(108838371/250000000 : ℝ)|=(108838371/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240252953/5000000000 : ℝ)|^8415 ≤ (6921550867403/20000000000000 : ℝ)^6367
        have hw : |(2240252953/5000000000 : ℝ)|=(2240252953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230100233/10000000000 : ℝ)|^8415 ≤ (4009342567701/12500000000000 : ℝ)^6367
        have hw : |(4230100233/10000000000 : ℝ)|=(4230100233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1222_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2291/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5727/50000 : ℝ) ^ (4207/1024 : ℝ) ≤ (6804420557609637/50000000000000000000 : ℝ) := by
    have hpowers : (5727/50000 : ℝ)^4207 ≤ (6804420557609637/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5727 : ℕ)^4207*50000000000000000000^1024 ≤ 6804420557609637^1024*50000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5727 50000 6804420557609637 50000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5727/50000 : ℝ)) (X := (6804420557609637/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7047/50000 : ℝ) ^ (4207/1024 : ℝ) ≤ (31907568689148179/100000000000000000000 : ℝ) := by
    have hpowers : (7047/50000 : ℝ)^4207 ≤ (31907568689148179/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7047 : ℕ)^4207*100000000000000000000^1024 ≤ 31907568689148179^1024*50000^4207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7047 50000 31907568689148179 100000000000000000000 4207 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7047/50000 : ℝ)) (X := (31907568689148179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006804420557609637/25000000000000000000 : ℝ) ≤ (10000662420664657/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (25006804420557609637/25000000000000000000 : ℝ)^1024 ≤ (10000662420664657/10000000000000000 : ℝ)^4207 := by
      have hnat : (25006804420557609637 : ℕ)^1024*10000000000000000^4207 ≤ 10000662420664657^4207*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006804420557609637 25000000000000000000 10000662420664657 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000662420664657/10000000000000000 : ℝ)) (X := (25006804420557609637/25000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045516409804367453/100000000000000000000 : ℝ) ≤ (400044307849123/400000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (100045516409804367453/100000000000000000000 : ℝ)^1024 ≤ (400044307849123/400000000000000 : ℝ)^4207 := by
      have hnat : (100045516409804367453 : ℕ)^1024*400000000000000^4207 ≤ 400044307849123^4207*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045516409804367453 100000000000000000000 400044307849123 400000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400044307849123/400000000000000 : ℝ)) (X := (100045516409804367453/100000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031907568689148179/50000000000000000000 : ℝ) ≤ (10001552971791493/10000000000000000 : ℝ) ^ (4207/1024 : ℝ) := by
    have hpowers : (50031907568689148179/50000000000000000000 : ℝ)^1024 ≤ (10001552971791493/10000000000000000 : ℝ)^4207 := by
      have hnat : (50031907568689148179 : ℕ)^1024*10000000000000000^4207 ≤ 10001552971791493^4207*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031907568689148179 50000000000000000000 10001552971791493 10000000000000000 1024 4207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001552971791493/10000000000000000 : ℝ)) (X := (50031907568689148179/50000000000000000000 : ℝ)) (by norm_num) 4207 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6804420557609637/50000000000000000000 : ℝ) ≤ ((1099647850747829789/1100000000000000000 : ℝ)+2*(74212593903/44000000000000 : ℝ)*(5727/50000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (1099647850747829789/1100000000000000000 : ℝ)+2*(74212593903/44000000000000 : ℝ)*(5727/50000 : ℝ)=(10000662420664657/10000000000000000 : ℝ) by norm_num, show 1+2*(6804420557609637/50000000000000000000 : ℝ)=(25006804420557609637/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31907568689148179/100000000000000000000 : ℝ)+(6804420557609637/50000000000000000000 : ℝ) ≤ ((1099647850747829789/1100000000000000000 : ℝ)+(74212593903/44000000000000 : ℝ)*((7047/50000 : ℝ)+(5727/50000 : ℝ)))^(4207/1024 : ℝ) := by
    rw [show (1099647850747829789/1100000000000000000 : ℝ)+(74212593903/44000000000000 : ℝ)*((7047/50000 : ℝ)+(5727/50000 : ℝ))=(400044307849123/400000000000000 : ℝ) by norm_num, show 1+(31907568689148179/100000000000000000000 : ℝ)+(6804420557609637/50000000000000000000 : ℝ)=(100045516409804367453/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31907568689148179/100000000000000000000 : ℝ) ≤ ((1099647850747829789/1100000000000000000 : ℝ)+2*(74212593903/44000000000000 : ℝ)*(7047/50000 : ℝ))^(4207/1024 : ℝ) := by
    rw [show (1099647850747829789/1100000000000000000 : ℝ)+2*(74212593903/44000000000000 : ℝ)*(7047/50000 : ℝ)=(10001552971791493/10000000000000000 : ℝ) by norm_num, show 1+2*(31907568689148179/100000000000000000000 : ℝ)=(50031907568689148179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1099647850747829789/1100000000000000000 : ℝ)*(X 1 0+X 2 0)+(74212593903/44000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (1099647850747829789/1100000000000000000 : ℝ)) (alpha := (74212593903/44000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1099647850747829789/1100000000000000000 : ℝ)*(X 0 1+X 2 1)+(74212593903/44000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (1099647850747829789/1100000000000000000 : ℝ)) (alpha := (74212593903/44000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1099647850747829789/1100000000000000000 : ℝ)*(X 0 2+X 1 2)+(74212593903/44000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4207/1024 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (1099647850747829789/1100000000000000000 : ℝ)) (alpha := (74212593903/44000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2129208647/10000000000 : ℝ)*X 0 0+(5391527537/10000000000 : ℝ)*X 0 1+(1316745359/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213776037/400000000 : ℝ)*X 1 0+(-2192360797/10000000000 : ℝ)*X 1 1+(1316745359/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344400953/10000000000 : ℝ)*X 2 0+(5266981409/10000000000 : ℝ)*X 2 1+(-548090199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353525433/10000000000 : ℝ)*X 0 0+(4229464291/10000000000 : ℝ)*X 0 1+(1120284871/2500000000 : ℝ)*X 0 2+(4353525433/10000000000 : ℝ)*X 1 0+(4229464291/10000000000 : ℝ)*X 1 1+(1120284871/2500000000 : ℝ)*X 1 2+(4353525433/10000000000 : ℝ)*X 2 0+(4229464291/10000000000 : ℝ)*X 2 1+(1120284871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064606733/5000000000 : ℝ)*X 0 0+(1053459073/2000000000 : ℝ)*X 0 1+(5391212379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312665581/10000000000 : ℝ)*X 1 0+(-1034064621/5000000000 : ℝ)*X 1 1+(2695606509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312665933/10000000000 : ℝ)*X 2 0+(5391212479/10000000000 : ℝ)*X 2 1+(-4136259/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108838371/250000000 : ℝ)*X 0 0+(2240252953/5000000000 : ℝ)*X 0 1+(4230100233/10000000000 : ℝ)*X 0 2+(108838371/250000000 : ℝ)*X 1 0+(2240252953/5000000000 : ℝ)*X 1 1+(4230100233/10000000000 : ℝ)*X 1 2+(108838371/250000000 : ℝ)*X 2 0+(2240252953/5000000000 : ℝ)*X 2 1+(4230100233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1222_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134572095784503454074125637/27500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (427650827/50000000000000 : ℝ)*(base19) + (840626723/100000000000000 : ℝ)*(base23) + (6064929/20000000000000 : ℝ)*(lower2) + (98331823/100000000000000 : ℝ)*(upper3) + (66243847/100000000000000 : ℝ)*(upper5) + (3000651079397811/50000000000000 : ℝ)*(major0) + (3000651079397811/50000000000000 : ℝ)*(major1) + (3000651079397811/50000000000000 : ℝ)*(major2) + (8029180228854301/100000000000000 : ℝ)*(sp0) + (2007301011014981/25000000000000 : ℝ)*(sp1) + (1605840811746971/20000000000000 : ℝ)*(sp2) + (49667333315531/1250000000000 : ℝ)*(sp3) + (24670507277/100000000000000 : ℝ)*(sp4) + (2517973897/20000000000000 : ℝ)*(sp7) + (794679851022393/20000000000000 : ℝ)*(f.failure) + (4014602449680789/50000000000000 : ℝ)*(f.sum) + (9000849894233/1100000000000000000000000000 : ℝ)*base65 + (435127689854483121/55000000000000000000000000000000 : ℝ)*base68 + (210072679014483121/55000000000000000000000000000000 : ℝ)*base70 + (317172660794483121/55000000000000000000000000000000 : ℝ)*base72 + (7602813418133/1100000000000000000000000000 : ℝ)*base73 + (180876525510516879/55000000000000000000000000000000 : ℝ)*base75 + (867786547880516879/55000000000000000000000000000000 : ℝ)*base77 + (1931240602269483121/55000000000000000000000000000000 : ℝ)*base80 + (114161826833/1100000000000000000000000000 : ℝ)*base81 + (4524177/1000000000000000000000 : ℝ)*base89 + (4524177/1000000000000000000000 : ℝ)*base91 + (4524177/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84898382054632804705445811/27500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20641617/3125000000000 : ℝ)*(base19) + (703574433/50000000000000 : ℝ)*(base23) + (643776729/100000000000000 : ℝ)*(lower1) + (114689239/100000000000000 : ℝ)*(upper2) + (84054611/50000000000000 : ℝ)*(upper3) + (3015843818019867/50000000000000 : ℝ)*(major0) + (3015843818019867/50000000000000 : ℝ)*(major1) + (3015843818019867/50000000000000 : ℝ)*(major2) + (6602977/1000000000000 : ℝ)*(sp1) + (9092022109/100000000000000 : ℝ)*(sp3) + (8069858008070403/100000000000000 : ℝ)*(sp4) + (6304575536907/78125000000 : ℝ)*(sp5) + (8069856600921537/100000000000000 : ℝ)*(sp6) + (998377017269953/25000000000000 : ℝ)*(sp7) + (1996758580550961/50000000000000 : ℝ)*(f.failure) + (8069858008070403/100000000000000 : ℝ)*(f.sum) + (107575444001/1100000000000000000000000000 : ℝ)*base65 + (723768246578943063/55000000000000000000000000000000 : ℝ)*base67 + (646591960413943063/55000000000000000000000000000000 : ℝ)*base69 + (763464108773943063/55000000000000000000000000000000 : ℝ)*base71 + (1564900882801/1100000000000000000000000000 : ℝ)*base73 + (1423123805451056937/55000000000000000000000000000000 : ℝ)*base76 + (1839417973081056937/55000000000000000000000000000000 : ℝ)*base78 + (346540949538943063/55000000000000000000000000000000 : ℝ)*base79 + (1698389973701/1100000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (12217929/2500000000000000000000 : ℝ)*base89 + (12217929/2500000000000000000000 : ℝ)*base91 + (12217929/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1222_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1222_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1222_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1222_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1222_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1222_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4207/1024 : ℝ) ≤ p) (hpb : p ≤ (8415/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75518489/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1222_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
