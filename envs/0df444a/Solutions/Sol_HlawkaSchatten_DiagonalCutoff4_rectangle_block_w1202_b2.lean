-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1202_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:52.008278+00:00
-- url     : https://prove2.me/submissions/1b796cf0-e3dc-4b03-a2d3-3e37c51f1143

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
theorem support_rectangle_w1202_s6_0 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069248217/5000000000 : ℝ)*x 0 + (2696093889/5000000000 : ℝ)*x 1 + (5266423897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069248217/5000000000 : ℝ)^8395 ≤ (13000295498473/100000000000000 : ℝ)^6347 := by
    have hnat : (1069248217 : ℕ)^8395*100000000000000^6347 ≤ 13000295498473^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069248217 5000000000 13000295498473 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696093889/5000000000 : ℝ)^8395 ≤ (44178712164169/100000000000000 : ℝ)^6347 := by
    have hnat : (2696093889 : ℕ)^8395*100000000000000^6347 ≤ 44178712164169^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696093889 5000000000 44178712164169 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266423897/10000000000 : ℝ)^8395 ≤ (42820992320087/100000000000000 : ℝ)^6347 := by
    have hnat : (5266423897 : ℕ)^8395*100000000000000^6347 ≤ 42820992320087^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266423897 10000000000 42820992320087 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069248217/5000000000 : ℝ), (2696093889/5000000000 : ℝ), (5266423897/10000000000 : ℝ)] ![(13000295498473/100000000000000 : ℝ), (44178712164169/100000000000000 : ℝ), (42820992320087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069248217/5000000000 : ℝ)|^8395 ≤ (13000295498473/100000000000000 : ℝ)^6347
        have hw : |(-1069248217/5000000000 : ℝ)|=(1069248217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696093889/5000000000 : ℝ)|^8395 ≤ (44178712164169/100000000000000 : ℝ)^6347
        have hw : |(2696093889/5000000000 : ℝ)|=(2696093889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266423897/10000000000 : ℝ)|^8395 ≤ (42820992320087/100000000000000 : ℝ)^6347
        have hw : |(5266423897/10000000000 : ℝ)|=(5266423897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s6_1 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344570721/10000000000 : ℝ)*x 0 + (-275284363/1250000000 : ℝ)*x 1 + (1053284791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344570721/10000000000 : ℝ)^8395 ≤ (1364482289179/3125000000000 : ℝ)^6347 := by
    have hnat : (5344570721 : ℕ)^8395*3125000000000^6347 ≤ 1364482289179^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344570721 10000000000 1364482289179 3125000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275284363/1250000000 : ℝ)^8395 ≤ (2703114755819/20000000000000 : ℝ)^6347 := by
    have hnat : (275284363 : ℕ)^8395*20000000000000^6347 ≤ 2703114755819^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275284363 1250000000 2703114755819 20000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053284791/2000000000 : ℝ)^8395 ≤ (10705248235963/25000000000000 : ℝ)^6347 := by
    have hnat : (1053284791 : ℕ)^8395*25000000000000^6347 ≤ 10705248235963^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053284791 2000000000 10705248235963 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344570721/10000000000 : ℝ), (-275284363/1250000000 : ℝ), (1053284791/2000000000 : ℝ)] ![(1364482289179/3125000000000 : ℝ), (2703114755819/20000000000000 : ℝ), (10705248235963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344570721/10000000000 : ℝ)|^8395 ≤ (1364482289179/3125000000000 : ℝ)^6347
        have hw : |(5344570721/10000000000 : ℝ)|=(5344570721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275284363/1250000000 : ℝ)|^8395 ≤ (2703114755819/20000000000000 : ℝ)^6347
        have hw : |(-275284363/1250000000 : ℝ)|=(275284363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053284791/2000000000 : ℝ)|^8395 ≤ (10705248235963/25000000000000 : ℝ)^6347
        have hw : |(1053284791/2000000000 : ℝ)|=(1053284791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s6_2 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83508919/156250000 : ℝ)*x 0 + (65830297/125000000 : ℝ)*x 1 + (-2202275037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83508919/156250000 : ℝ)^8395 ≤ (43663434280279/100000000000000 : ℝ)^6347 := by
    have hnat : (83508919 : ℕ)^8395*100000000000000^6347 ≤ 43663434280279^6347*156250000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83508919 156250000 43663434280279 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65830297/125000000 : ℝ)^8395 ≤ (42820990846711/100000000000000 : ℝ)^6347 := by
    have hnat : (65830297 : ℕ)^8395*100000000000000^6347 ≤ 42820990846711^6347*125000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65830297 125000000 42820990846711 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202275037/10000000000 : ℝ)^8395 ≤ (844723428669/6250000000000 : ℝ)^6347 := by
    have hnat : (2202275037 : ℕ)^8395*6250000000000^6347 ≤ 844723428669^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202275037 10000000000 844723428669 6250000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83508919/156250000 : ℝ), (65830297/125000000 : ℝ), (-2202275037/10000000000 : ℝ)] ![(43663434280279/100000000000000 : ℝ), (42820990846711/100000000000000 : ℝ), (844723428669/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83508919/156250000 : ℝ)|^8395 ≤ (43663434280279/100000000000000 : ℝ)^6347
        have hw : |(83508919/156250000 : ℝ)|=(83508919/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65830297/125000000 : ℝ)|^8395 ≤ (42820990846711/100000000000000 : ℝ)^6347
        have hw : |(65830297/125000000 : ℝ)|=(65830297/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202275037/10000000000 : ℝ)|^8395 ≤ (844723428669/6250000000000 : ℝ)^6347
        have hw : |(-2202275037/10000000000 : ℝ)|=(2202275037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s6_3 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178138197/5000000000 : ℝ)*x 0 + (1057876073/2500000000 : ℝ)*x 1 + (70072763/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178138197/5000000000 : ℝ)^8395 ≤ (16658582259377/50000000000000 : ℝ)^6347 := by
    have hnat : (2178138197 : ℕ)^8395*50000000000000^6347 ≤ 16658582259377^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178138197 5000000000 16658582259377 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057876073/2500000000 : ℝ)^8395 ≤ (16030426143071/50000000000000 : ℝ)^6347 := by
    have hnat : (1057876073 : ℕ)^8395*50000000000000^6347 ≤ 16030426143071^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057876073 2500000000 16030426143071 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70072763/156250000 : ℝ)^8395 ≤ (8655495796471/25000000000000 : ℝ)^6347 := by
    have hnat : (70072763 : ℕ)^8395*25000000000000^6347 ≤ 8655495796471^6347*156250000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70072763 156250000 8655495796471 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178138197/5000000000 : ℝ), (1057876073/2500000000 : ℝ), (70072763/156250000 : ℝ)] ![(16658582259377/50000000000000 : ℝ), (16030426143071/50000000000000 : ℝ), (8655495796471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178138197/5000000000 : ℝ)|^8395 ≤ (16658582259377/50000000000000 : ℝ)^6347
        have hw : |(2178138197/5000000000 : ℝ)|=(2178138197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057876073/2500000000 : ℝ)|^8395 ≤ (16030426143071/50000000000000 : ℝ)^6347
        have hw : |(1057876073/2500000000 : ℝ)|=(1057876073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70072763/156250000 : ℝ)|^8395 ≤ (8655495796471/25000000000000 : ℝ)^6347
        have hw : |(70072763/156250000 : ℝ)|=(70072763/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s6_4 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-33414083/156250000 : ℝ)*x 0 + (5266741671/10000000000 : ℝ)*x 1 + (5391868789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33414083/156250000 : ℝ)^8395 ≤ (812520920081/6250000000000 : ℝ)^6347 := by
    have hnat : (33414083 : ℕ)^8395*6250000000000^6347 ≤ 812520920081^6347*156250000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33414083 156250000 812520920081 6250000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266741671/10000000000 : ℝ)^8395 ≤ (42824409876603/100000000000000 : ℝ)^6347 := by
    have hnat : (5266741671 : ℕ)^8395*100000000000000^6347 ≤ 42824409876603^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266741671 10000000000 42824409876603 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391868789/10000000000 : ℝ)^8395 ≤ (4417525538363/10000000000000 : ℝ)^6347 := by
    have hnat : (5391868789 : ℕ)^8395*10000000000000^6347 ≤ 4417525538363^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391868789 10000000000 4417525538363 10000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33414083/156250000 : ℝ), (5266741671/10000000000 : ℝ), (5391868789/10000000000 : ℝ)] ![(812520920081/6250000000000 : ℝ), (42824409876603/100000000000000 : ℝ), (4417525538363/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33414083/156250000 : ℝ)|^8395 ≤ (812520920081/6250000000000 : ℝ)^6347
        have hw : |(-33414083/156250000 : ℝ)|=(33414083/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266741671/10000000000 : ℝ)|^8395 ≤ (42824409876603/100000000000000 : ℝ)^6347
        have hw : |(5266741671/10000000000 : ℝ)|=(5266741671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391868789/10000000000 : ℝ)|^8395 ≤ (4417525538363/10000000000000 : ℝ)^6347
        have hw : |(5391868789/10000000000 : ℝ)|=(5391868789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s6_5 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312569789/10000000000 : ℝ)*x 0 + (-8112617/39062500 : ℝ)*x 1 + (215674753/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312569789/10000000000 : ℝ)^8395 ≤ (21658985907299/50000000000000 : ℝ)^6347 := by
    have hnat : (5312569789 : ℕ)^8395*50000000000000^6347 ≤ 21658985907299^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312569789 10000000000 21658985907299 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8112617/39062500 : ℝ)^8395 ≤ (12506772396317/100000000000000 : ℝ)^6347 := by
    have hnat : (8112617 : ℕ)^8395*100000000000000^6347 ≤ 12506772396317^6347*39062500^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8112617 39062500 12506772396317 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215674753/400000000 : ℝ)^8395 ≤ (44175255773747/100000000000000 : ℝ)^6347 := by
    have hnat : (215674753 : ℕ)^8395*100000000000000^6347 ≤ 44175255773747^6347*400000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215674753 400000000 44175255773747 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312569789/10000000000 : ℝ), (-8112617/39062500 : ℝ), (215674753/400000000 : ℝ)] ![(21658985907299/50000000000000 : ℝ), (12506772396317/100000000000000 : ℝ), (44175255773747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312569789/10000000000 : ℝ)|^8395 ≤ (21658985907299/50000000000000 : ℝ)^6347
        have hw : |(5312569789/10000000000 : ℝ)|=(5312569789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8112617/39062500 : ℝ)|^8395 ≤ (12506772396317/100000000000000 : ℝ)^6347
        have hw : |(-8112617/39062500 : ℝ)|=(8112617/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215674753/400000000 : ℝ)|^8395 ≤ (44175255773747/100000000000000 : ℝ)^6347
        have hw : |(215674753/400000000 : ℝ)|=(215674753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s6_6 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656284909/5000000000 : ℝ)*x 0 + (2695934399/5000000000 : ℝ)*x 1 + (-2076829949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656284909/5000000000 : ℝ)^8395 ≤ (43317972127359/100000000000000 : ℝ)^6347 := by
    have hnat : (2656284909 : ℕ)^8395*100000000000000^6347 ≤ 43317972127359^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656284909 5000000000 43317972127359 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695934399/5000000000 : ℝ)^8395 ≤ (44175255481159/100000000000000 : ℝ)^6347 := by
    have hnat : (2695934399 : ℕ)^8395*100000000000000^6347 ≤ 44175255481159^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695934399 5000000000 44175255481159 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076829949/10000000000 : ℝ)^8395 ≤ (6253386186211/50000000000000 : ℝ)^6347 := by
    have hnat : (2076829949 : ℕ)^8395*50000000000000^6347 ≤ 6253386186211^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076829949 10000000000 6253386186211 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656284909/5000000000 : ℝ), (2695934399/5000000000 : ℝ), (-2076829949/10000000000 : ℝ)] ![(43317972127359/100000000000000 : ℝ), (44175255481159/100000000000000 : ℝ), (6253386186211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656284909/5000000000 : ℝ)|^8395 ≤ (43317972127359/100000000000000 : ℝ)^6347
        have hw : |(2656284909/5000000000 : ℝ)|=(2656284909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695934399/5000000000 : ℝ)|^8395 ≤ (44175255481159/100000000000000 : ℝ)^6347
        have hw : |(2695934399/5000000000 : ℝ)|=(2695934399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2076829949/10000000000 : ℝ)|^8395 ≤ (6253386186211/50000000000000 : ℝ)^6347
        have hw : |(-2076829949/10000000000 : ℝ)|=(2076829949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s6_7 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089071459/2500000000 : ℝ)*x 0 + (224200847/500000000 : ℝ)*x 1 + (4232146733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089071459/2500000000 : ℝ)^8395 ≤ (33317260033177/100000000000000 : ℝ)^6347 := by
    have hnat : (1089071459 : ℕ)^8395*100000000000000^6347 ≤ 33317260033177^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089071459 2500000000 33317260033177 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224200847/500000000 : ℝ)^8395 ≤ (34615449299029/100000000000000 : ℝ)^6347 := by
    have hnat : (224200847 : ℕ)^8395*100000000000000^6347 ≤ 34615449299029^6347*500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224200847 500000000 34615449299029 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232146733/10000000000 : ℝ)^8395 ≤ (8016822665649/25000000000000 : ℝ)^6347 := by
    have hnat : (4232146733 : ℕ)^8395*25000000000000^6347 ≤ 8016822665649^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232146733 10000000000 8016822665649 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089071459/2500000000 : ℝ), (224200847/500000000 : ℝ), (4232146733/10000000000 : ℝ)] ![(33317260033177/100000000000000 : ℝ), (34615449299029/100000000000000 : ℝ), (8016822665649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089071459/2500000000 : ℝ)|^8395 ≤ (33317260033177/100000000000000 : ℝ)^6347
        have hw : |(1089071459/2500000000 : ℝ)|=(1089071459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224200847/500000000 : ℝ)|^8395 ≤ (34615449299029/100000000000000 : ℝ)^6347
        have hw : |(224200847/500000000 : ℝ)|=(224200847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232146733/10000000000 : ℝ)|^8395 ≤ (8016822665649/25000000000000 : ℝ)^6347
        have hw : |(4232146733/10000000000 : ℝ)|=(4232146733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1202_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    (357/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
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
  have lower0 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/500 : ℝ) ^ (4197/1024 : ℝ) ≤ (3408311555974901/25000000000000000000 : ℝ) := by
    have hpowers : (57/500 : ℝ)^4197 ≤ (3408311555974901/25000000000000000000 : ℝ)^1024 := by
      have hnat : (57 : ℕ)^4197*25000000000000000000^1024 ≤ 3408311555974901^1024*500^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 500 3408311555974901 25000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/500 : ℝ)) (X := (3408311555974901/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (4197/1024 : ℝ) ≤ (32713578330555243/100000000000000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^4197 ≤ (32713578330555243/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7057 : ℕ)^4197*100000000000000000000^1024 ≤ 32713578330555243^1024*50000^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 32713578330555243 100000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (32713578330555243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503408311555974901/12500000000000000000 : ℝ) ≤ (1250083148710187/1250000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (12503408311555974901/12500000000000000000 : ℝ)^1024 ≤ (1250083148710187/1250000000000000 : ℝ)^4197 := by
      have hnat : (12503408311555974901 : ℕ)^1024*1250000000000000^4197 ≤ 1250083148710187^4197*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503408311555974901 12500000000000000000 1250083148710187 1250000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250083148710187/1250000000000000 : ℝ)) (X := (12503408311555974901/12500000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046346824554454847/100000000000000000000 : ℝ) ≤ (10001130589373481/10000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (100046346824554454847/100000000000000000000 : ℝ)^1024 ≤ (10001130589373481/10000000000000000 : ℝ)^4197 := by
      have hnat : (100046346824554454847 : ℕ)^1024*10000000000000000^4197 ≤ 10001130589373481^4197*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046346824554454847 100000000000000000000 10001130589373481 10000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001130589373481/10000000000000000 : ℝ)) (X := (100046346824554454847/100000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032713578330555243/50000000000000000000 : ℝ) ≤ (5000797994532733/5000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (50032713578330555243/50000000000000000000 : ℝ)^1024 ≤ (5000797994532733/5000000000000000 : ℝ)^4197 := by
      have hnat : (50032713578330555243 : ℕ)^1024*5000000000000000^4197 ≤ 5000797994532733^4197*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032713578330555243 50000000000000000000 5000797994532733 5000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000797994532733/5000000000000000 : ℝ)) (X := (50032713578330555243/50000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3408311555974901/25000000000000000000 : ℝ) ≤ ((847849819119322567/848125000000000000 : ℝ)+2*(93079938397/54280000000000 : ℝ)*(57/500 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (847849819119322567/848125000000000000 : ℝ)+2*(93079938397/54280000000000 : ℝ)*(57/500 : ℝ)=(1250083148710187/1250000000000000 : ℝ) by norm_num, show 1+2*(3408311555974901/25000000000000000000 : ℝ)=(12503408311555974901/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32713578330555243/100000000000000000000 : ℝ)+(3408311555974901/25000000000000000000 : ℝ) ≤ ((847849819119322567/848125000000000000 : ℝ)+(93079938397/54280000000000 : ℝ)*((7057/50000 : ℝ)+(57/500 : ℝ)))^(4197/1024 : ℝ) := by
    rw [show (847849819119322567/848125000000000000 : ℝ)+(93079938397/54280000000000 : ℝ)*((7057/50000 : ℝ)+(57/500 : ℝ))=(10001130589373481/10000000000000000 : ℝ) by norm_num, show 1+(32713578330555243/100000000000000000000 : ℝ)+(3408311555974901/25000000000000000000 : ℝ)=(100046346824554454847/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32713578330555243/100000000000000000000 : ℝ) ≤ ((847849819119322567/848125000000000000 : ℝ)+2*(93079938397/54280000000000 : ℝ)*(7057/50000 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (847849819119322567/848125000000000000 : ℝ)+2*(93079938397/54280000000000 : ℝ)*(7057/50000 : ℝ)=(5000797994532733/5000000000000000 : ℝ) by norm_num, show 1+2*(32713578330555243/100000000000000000000 : ℝ)=(50032713578330555243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (847849819119322567/848125000000000000 : ℝ)*(X 1 0+X 2 0)+(93079938397/54280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (57/500 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (847849819119322567/848125000000000000 : ℝ)) (alpha := (93079938397/54280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (847849819119322567/848125000000000000 : ℝ)*(X 0 1+X 2 1)+(93079938397/54280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (57/500 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (847849819119322567/848125000000000000 : ℝ)) (alpha := (93079938397/54280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (847849819119322567/848125000000000000 : ℝ)*(X 0 2+X 1 2)+(93079938397/54280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (57/500 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (847849819119322567/848125000000000000 : ℝ)) (alpha := (93079938397/54280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1069248217/5000000000 : ℝ)*X 0 0+(2696093889/5000000000 : ℝ)*X 0 1+(5266423897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344570721/10000000000 : ℝ)*X 1 0+(-275284363/1250000000 : ℝ)*X 1 1+(1053284791/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83508919/156250000 : ℝ)*X 2 0+(65830297/125000000 : ℝ)*X 2 1+(-2202275037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178138197/5000000000 : ℝ)*X 0 0+(1057876073/2500000000 : ℝ)*X 0 1+(70072763/156250000 : ℝ)*X 0 2+(2178138197/5000000000 : ℝ)*X 1 0+(1057876073/2500000000 : ℝ)*X 1 1+(70072763/156250000 : ℝ)*X 1 2+(2178138197/5000000000 : ℝ)*X 2 0+(1057876073/2500000000 : ℝ)*X 2 1+(70072763/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33414083/156250000 : ℝ)*X 0 0+(5266741671/10000000000 : ℝ)*X 0 1+(5391868789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312569789/10000000000 : ℝ)*X 1 0+(-8112617/39062500 : ℝ)*X 1 1+(215674753/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656284909/5000000000 : ℝ)*X 2 0+(2695934399/5000000000 : ℝ)*X 2 1+(-2076829949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089071459/2500000000 : ℝ)*X 0 0+(224200847/500000000 : ℝ)*X 0 1+(4232146733/10000000000 : ℝ)*X 0 2+(1089071459/2500000000 : ℝ)*X 1 0+(224200847/500000000 : ℝ)*X 1 1+(4232146733/10000000000 : ℝ)*X 1 2+(1089071459/2500000000 : ℝ)*X 2 0+(224200847/500000000 : ℝ)*X 2 1+(4232146733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (426649572565556909525739531/42406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180818803/10000000000000 : ℝ)*(base19) + (808999559/50000000000000 : ℝ)*(base23) + (95963573/50000000000000 : ℝ)*(lower2) + (433740021/100000000000000 : ℝ)*(upper3) + (14740121/100000000000000 : ℝ)*(lower4) + (5950870027169169/100000000000000 : ℝ)*(major0) + (5950870027169169/100000000000000 : ℝ)*(major1) + (5950870027169169/100000000000000 : ℝ)*(major2) + (7951460703603169/100000000000000 : ℝ)*(sp0) + (496968514150429/6250000000000 : ℝ)*(sp1) + (124242131509309/1562500000000 : ℝ)*(sp2) + (1975104430039689/50000000000000 : ℝ)*(sp3) + (1493239669/4000000000000 : ℝ)*(sp4) + (8206074291/25000000000000 : ℝ)*(sp7) + (1975120842188271/50000000000000 : ℝ)*(f.failure) + (3975749017297447/50000000000000 : ℝ)*(f.sum) + (17967524646233/2714000000000000000000000000 : ℝ)*base65 + (147115684486997181/10601562500000000000000000000000 : ℝ)*base67 + (264879915906958763/21203125000000000000000000000000 : ℝ)*base70 + (115959491038697487/21203125000000000000000000000000 : ℝ)*base71 + (4429972018627/2714000000000000000000000000 : ℝ)*base74 + (147726851269677513/21203125000000000000000000000000 : ℝ)*base76 + (113613486708947487/21203125000000000000000000000000 : ℝ)*base77 + (150378835197884987/21203125000000000000000000000000 : ℝ)*base79 + (5090130644949/2714000000000000000000000000 : ℝ)*base81 + (258753/125000000000000000000 : ℝ)*base89 + (258753/125000000000000000000 : ℝ)*base91 + (258753/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4200357790105864372445019/2120312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (174442671/50000000000000 : ℝ)*(base19) + (398191787/100000000000000 : ℝ)*(base23) + (45159837/100000000000000 : ℝ)*(upper3) + (63971/100000000000000 : ℝ)*(lower4) + (34231533/100000000000000 : ℝ)*(upper5) + (149527151157797/2500000000000 : ℝ)*(major0) + (149527151157797/2500000000000 : ℝ)*(major1) + (149527151157797/2500000000000 : ℝ)*(major2) + (11509585563/100000000000000 : ℝ)*(sp1) + (12432655491/100000000000000 : ℝ)*(sp2) + (3995936336851589/50000000000000 : ℝ)*(sp4) + (499491300952017/6250000000000 : ℝ)*(sp5) + (7991859842855899/100000000000000 : ℝ)*(sp6) + (1985149676443473/50000000000000 : ℝ)*(sp7) + (1985149676443473/50000000000000 : ℝ)*(f.failure) + (3995936336851589/50000000000000 : ℝ)*(f.sum) + (634472002747/67850000000000000000000000 : ℝ)*base65 + (8485795110138851/2120312500000000000000000000000 : ℝ)*base68 + (11790746959736613/1060156250000000000000000000000 : ℝ)*base70 + (2605540448119173/4240625000000000000000000000000 : ℝ)*base71 + (428127402593/339250000000000000000000000 : ℝ)*base73 + (34982940137105827/4240625000000000000000000000000 : ℝ)*base76 + (13108086063123649/2120312500000000000000000000000 : ℝ)*base77 + (28135738458995101/2120312500000000000000000000000 : ℝ)*base80 + (43743314469/16962500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (734639/125000000000000000000 : ℝ)*base89 + (734639/125000000000000000000 : ℝ)*base91 + (734639/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1202_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1202_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1202_s7_0 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138520433/10000000000 : ℝ)*x 0 + (2695971723/5000000000 : ℝ)*x 1 + (105333043/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138520433/10000000000 : ℝ)^8395 ≤ (13000488468931/100000000000000 : ℝ)^6347 := by
    have hnat : (2138520433 : ℕ)^8395*100000000000000^6347 ≤ 13000488468931^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138520433 10000000000 13000488468931 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695971723/5000000000 : ℝ)^8395 ≤ (22088032205729/50000000000000 : ℝ)^6347 := by
    have hnat : (2695971723 : ℕ)^8395*50000000000000^6347 ≤ 22088032205729^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695971723 5000000000 22088032205729 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105333043/200000000 : ℝ)^8395 ≤ (42823447100491/100000000000000 : ℝ)^6347 := by
    have hnat : (105333043 : ℕ)^8395*100000000000000^6347 ≤ 42823447100491^6347*200000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105333043 200000000 42823447100491 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138520433/10000000000 : ℝ), (2695971723/5000000000 : ℝ), (105333043/200000000 : ℝ)] ![(13000488468931/100000000000000 : ℝ), (22088032205729/50000000000000 : ℝ), (42823447100491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138520433/10000000000 : ℝ)|^8395 ≤ (13000488468931/100000000000000 : ℝ)^6347
        have hw : |(-2138520433/10000000000 : ℝ)|=(2138520433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695971723/5000000000 : ℝ)|^8395 ≤ (22088032205729/50000000000000 : ℝ)^6347
        have hw : |(2695971723/5000000000 : ℝ)|=(2695971723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105333043/200000000 : ℝ)|^8395 ≤ (42823447100491/100000000000000 : ℝ)^6347
        have hw : |(105333043/200000000 : ℝ)|=(105333043/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s7_1 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672253917/5000000000 : ℝ)*x 0 + (-2202055977/10000000000 : ℝ)*x 1 + (263332619/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672253917/5000000000 : ℝ)^8395 ≤ (10915688427539/25000000000000 : ℝ)^6347 := by
    have hnat : (2672253917 : ℕ)^8395*25000000000000^6347 ≤ 10915688427539^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672253917 5000000000 10915688427539 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202055977/10000000000 : ℝ)^8395 ≤ (13513796696881/100000000000000 : ℝ)^6347 := by
    have hnat : (2202055977 : ℕ)^8395*100000000000000^6347 ≤ 13513796696881^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202055977 10000000000 13513796696881 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263332619/500000000 : ℝ)^8395 ≤ (42823449574077/100000000000000 : ℝ)^6347 := by
    have hnat : (263332619 : ℕ)^8395*100000000000000^6347 ≤ 42823449574077^6347*500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263332619 500000000 42823449574077 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672253917/5000000000 : ℝ), (-2202055977/10000000000 : ℝ), (263332619/500000000 : ℝ)] ![(10915688427539/25000000000000 : ℝ), (13513796696881/100000000000000 : ℝ), (42823449574077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672253917/5000000000 : ℝ)|^8395 ≤ (10915688427539/25000000000000 : ℝ)^6347
        have hw : |(2672253917/5000000000 : ℝ)|=(2672253917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202055977/10000000000 : ℝ)|^8395 ≤ (13513796696881/100000000000000 : ℝ)^6347
        have hw : |(-2202055977/10000000000 : ℝ)|=(2202055977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263332619/500000000 : ℝ)|^8395 ≤ (42823449574077/100000000000000 : ℝ)^6347
        have hw : |(263332619/500000000 : ℝ)|=(263332619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s7_2 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336126973/2500000000 : ℝ)*x 0 + (2633326307/5000000000 : ℝ)*x 1 + (-2202055589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336126973/2500000000 : ℝ)^8395 ≤ (43662754336891/100000000000000 : ℝ)^6347 := by
    have hnat : (1336126973 : ℕ)^8395*100000000000000^6347 ≤ 43662754336891^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336126973 2500000000 43662754336891 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633326307/5000000000 : ℝ)^8395 ≤ (21411726045341/50000000000000 : ℝ)^6347 := by
    have hnat : (2633326307 : ℕ)^8395*50000000000000^6347 ≤ 21411726045341^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633326307 5000000000 21411726045341 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202055589/10000000000 : ℝ)^8395 ≤ (13513793547443/100000000000000 : ℝ)^6347 := by
    have hnat : (2202055589 : ℕ)^8395*100000000000000^6347 ≤ 13513793547443^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202055589 10000000000 13513793547443 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336126973/2500000000 : ℝ), (2633326307/5000000000 : ℝ), (-2202055589/10000000000 : ℝ)] ![(43662754336891/100000000000000 : ℝ), (21411726045341/50000000000000 : ℝ), (13513793547443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336126973/2500000000 : ℝ)|^8395 ≤ (43662754336891/100000000000000 : ℝ)^6347
        have hw : |(1336126973/2500000000 : ℝ)|=(1336126973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633326307/5000000000 : ℝ)|^8395 ≤ (21411726045341/50000000000000 : ℝ)^6347
        have hw : |(2633326307/5000000000 : ℝ)|=(2633326307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202055589/10000000000 : ℝ)|^8395 ≤ (13513793547443/100000000000000 : ℝ)^6347
        have hw : |(-2202055589/10000000000 : ℝ)|=(2202055589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s7_3 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435628853/1000000000 : ℝ)*x 0 + (4231978741/10000000000 : ℝ)*x 1 + (896835831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435628853/1000000000 : ℝ)^8395 ≤ (33317287285451/100000000000000 : ℝ)^6347 := by
    have hnat : (435628853 : ℕ)^8395*100000000000000^6347 ≤ 33317287285451^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435628853 1000000000 33317287285451 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231978741/10000000000 : ℝ)^8395 ≤ (32065607060053/100000000000000 : ℝ)^6347 := by
    have hnat : (4231978741 : ℕ)^8395*100000000000000^6347 ≤ 32065607060053^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231978741 10000000000 32065607060053 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896835831/2000000000 : ℝ)^8395 ≤ (34617105635163/100000000000000 : ℝ)^6347 := by
    have hnat : (896835831 : ℕ)^8395*100000000000000^6347 ≤ 34617105635163^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896835831 2000000000 34617105635163 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435628853/1000000000 : ℝ), (4231978741/10000000000 : ℝ), (896835831/2000000000 : ℝ)] ![(33317287285451/100000000000000 : ℝ), (32065607060053/100000000000000 : ℝ), (34617105635163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435628853/1000000000 : ℝ)|^8395 ≤ (33317287285451/100000000000000 : ℝ)^6347
        have hw : |(435628853/1000000000 : ℝ)|=(435628853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231978741/10000000000 : ℝ)|^8395 ≤ (32065607060053/100000000000000 : ℝ)^6347
        have hw : |(4231978741/10000000000 : ℝ)|=(4231978741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896835831/2000000000 : ℝ)|^8395 ≤ (34617105635163/100000000000000 : ℝ)^6347
        have hw : |(896835831/2000000000 : ℝ)|=(896835831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s7_4 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069262473/5000000000 : ℝ)*x 0 + (329185487/625000000 : ℝ)*x 1 + (1078325367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069262473/5000000000 : ℝ)^8395 ≤ (812532797313/6250000000000 : ℝ)^6347 := by
    have hnat : (1069262473 : ℕ)^8395*6250000000000^6347 ≤ 812532797313^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069262473 5000000000 812532797313 6250000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329185487/625000000 : ℝ)^8395 ≤ (42826841775287/100000000000000 : ℝ)^6347 := by
    have hnat : (329185487 : ℕ)^8395*100000000000000^6347 ≤ 42826841775287^6347*625000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329185487 625000000 42826841775287 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078325367/2000000000 : ℝ)^8395 ≤ (44172633450459/100000000000000 : ℝ)^6347 := by
    have hnat : (1078325367 : ℕ)^8395*100000000000000^6347 ≤ 44172633450459^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078325367 2000000000 44172633450459 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069262473/5000000000 : ℝ), (329185487/625000000 : ℝ), (1078325367/2000000000 : ℝ)] ![(812532797313/6250000000000 : ℝ), (42826841775287/100000000000000 : ℝ), (44172633450459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069262473/5000000000 : ℝ)|^8395 ≤ (812532797313/6250000000000 : ℝ)^6347
        have hw : |(-1069262473/5000000000 : ℝ)|=(1069262473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329185487/625000000 : ℝ)|^8395 ≤ (42826841775287/100000000000000 : ℝ)^6347
        have hw : |(329185487/625000000 : ℝ)|=(329185487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078325367/2000000000 : ℝ)|^8395 ≤ (44172633450459/100000000000000 : ℝ)^6347
        have hw : |(1078325367/2000000000 : ℝ)|=(1078325367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s7_5 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062525523/2000000000 : ℝ)*x 0 + (-415416127/2000000000 : ℝ)*x 1 + (539162701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062525523/2000000000 : ℝ)^8395 ≤ (10829648865667/25000000000000 : ℝ)^6347 := by
    have hnat : (1062525523 : ℕ)^8395*25000000000000^6347 ≤ 10829648865667^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062525523 2000000000 10829648865667 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415416127/2000000000 : ℝ)^8395 ≤ (12508769174627/100000000000000 : ℝ)^6347 := by
    have hnat : (415416127 : ℕ)^8395*100000000000000^6347 ≤ 12508769174627^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415416127 2000000000 12508769174627 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539162701/1000000000 : ℝ)^8395 ≤ (2760789709177/6250000000000 : ℝ)^6347 := by
    have hnat : (539162701 : ℕ)^8395*6250000000000^6347 ≤ 2760789709177^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539162701 1000000000 2760789709177 6250000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062525523/2000000000 : ℝ), (-415416127/2000000000 : ℝ), (539162701/1000000000 : ℝ)] ![(10829648865667/25000000000000 : ℝ), (12508769174627/100000000000000 : ℝ), (2760789709177/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062525523/2000000000 : ℝ)|^8395 ≤ (10829648865667/25000000000000 : ℝ)^6347
        have hw : |(1062525523/2000000000 : ℝ)|=(1062525523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415416127/2000000000 : ℝ)|^8395 ≤ (12508769174627/100000000000000 : ℝ)^6347
        have hw : |(-415416127/2000000000 : ℝ)|=(415416127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539162701/1000000000 : ℝ)|^8395 ≤ (2760789709177/6250000000000 : ℝ)^6347
        have hw : |(539162701/1000000000 : ℝ)|=(539162701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s7_6 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312627417/10000000000 : ℝ)*x 0 + (5391627163/10000000000 : ℝ)*x 1 + (-259635087/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312627417/10000000000 : ℝ)^8395 ≤ (10829648331813/25000000000000 : ℝ)^6347 := by
    have hnat : (5312627417 : ℕ)^8395*25000000000000^6347 ≤ 10829648331813^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312627417 10000000000 10829648331813 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391627163/10000000000 : ℝ)^8395 ≤ (44172637004803/100000000000000 : ℝ)^6347 := by
    have hnat : (5391627163 : ℕ)^8395*100000000000000^6347 ≤ 44172637004803^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391627163 10000000000 44172637004803 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259635087/1250000000 : ℝ)^8395 ≤ (12508769660523/100000000000000 : ℝ)^6347 := by
    have hnat : (259635087 : ℕ)^8395*100000000000000^6347 ≤ 12508769660523^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259635087 1250000000 12508769660523 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312627417/10000000000 : ℝ), (5391627163/10000000000 : ℝ), (-259635087/1250000000 : ℝ)] ![(10829648331813/25000000000000 : ℝ), (44172637004803/100000000000000 : ℝ), (12508769660523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312627417/10000000000 : ℝ)|^8395 ≤ (10829648331813/25000000000000 : ℝ)^6347
        have hw : |(5312627417/10000000000 : ℝ)|=(5312627417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391627163/10000000000 : ℝ)|^8395 ≤ (44172637004803/100000000000000 : ℝ)^6347
        have hw : |(5391627163/10000000000 : ℝ)|=(5391627163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259635087/1250000000 : ℝ)|^8395 ≤ (12508769660523/100000000000000 : ℝ)^6347
        have hw : |(-259635087/1250000000 : ℝ)|=(259635087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s7_7 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871259599/2000000000 : ℝ)*x 0 + (4483544261/10000000000 : ℝ)*x 1 + (2116308011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871259599/2000000000 : ℝ)^8395 ≤ (16658691516313/50000000000000 : ℝ)^6347 := by
    have hnat : (871259599 : ℕ)^8395*50000000000000^6347 ≤ 16658691516313^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871259599 2000000000 16658691516313 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483544261/10000000000 : ℝ)^8395 ≤ (13519774611/39062500000 : ℝ)^6347 := by
    have hnat : (4483544261 : ℕ)^8395*39062500000^6347 ≤ 13519774611^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483544261 10000000000 13519774611 39062500000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116308011/5000000000 : ℝ)^8395 ≤ (32071993954111/100000000000000 : ℝ)^6347 := by
    have hnat : (2116308011 : ℕ)^8395*100000000000000^6347 ≤ 32071993954111^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116308011 5000000000 32071993954111 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871259599/2000000000 : ℝ), (4483544261/10000000000 : ℝ), (2116308011/5000000000 : ℝ)] ![(16658691516313/50000000000000 : ℝ), (13519774611/39062500000 : ℝ), (32071993954111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871259599/2000000000 : ℝ)|^8395 ≤ (16658691516313/50000000000000 : ℝ)^6347
        have hw : |(871259599/2000000000 : ℝ)|=(871259599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483544261/10000000000 : ℝ)|^8395 ≤ (13519774611/39062500000 : ℝ)^6347
        have hw : |(4483544261/10000000000 : ℝ)|=(4483544261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116308011/5000000000 : ℝ)|^8395 ≤ (32071993954111/100000000000000 : ℝ)^6347
        have hw : |(2116308011/5000000000 : ℝ)|=(2116308011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1202_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11429/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (357/3125 : ℝ) ^ (4197/1024 : ℝ) ≤ (13751267689434571/100000000000000000000 : ℝ) := by
    have hpowers : (357/3125 : ℝ)^4197 ≤ (13751267689434571/100000000000000000000 : ℝ)^1024 := by
      have hnat : (357 : ℕ)^4197*100000000000000000000^1024 ≤ 13751267689434571^1024*3125^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        357 3125 13751267689434571 100000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (357/3125 : ℝ)) (X := (13751267689434571/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1761/12500 : ℝ) ^ (4197/1024 : ℝ) ≤ (8116821537397207/25000000000000000000 : ℝ) := by
    have hpowers : (1761/12500 : ℝ)^4197 ≤ (8116821537397207/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1761 : ℕ)^4197*25000000000000000000^1024 ≤ 8116821537397207^1024*12500^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 12500 8116821537397207 25000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/12500 : ℝ)) (X := (8116821537397207/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013751267689434571/50000000000000000000 : ℝ) ≤ (2500167736888639/2500000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (50013751267689434571/50000000000000000000 : ℝ)^1024 ≤ (2500167736888639/2500000000000000 : ℝ)^4197 := by
      have hnat : (50013751267689434571 : ℕ)^1024*2500000000000000^4197 ≤ 2500167736888639^4197*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013751267689434571 50000000000000000000 2500167736888639 2500000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500167736888639/2500000000000000 : ℝ)) (X := (50013751267689434571/50000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046218553839023399/100000000000000000000 : ℝ) ≤ (2000225492174093/2000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (100046218553839023399/100000000000000000000 : ℝ)^1024 ≤ (2000225492174093/2000000000000000 : ℝ)^4197 := by
      have hnat : (100046218553839023399 : ℕ)^1024*2000000000000000^4197 ≤ 2000225492174093^4197*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046218553839023399 100000000000000000000 2000225492174093 2000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000225492174093/2000000000000000 : ℝ)) (X := (100046218553839023399/100000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508116821537397207/12500000000000000000 : ℝ) ≤ (5000791987093187/5000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (12508116821537397207/12500000000000000000 : ℝ)^1024 ≤ (5000791987093187/5000000000000000 : ℝ)^4197 := by
      have hnat : (12508116821537397207 : ℕ)^1024*5000000000000000^4197 ≤ 5000791987093187^4197*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508116821537397207 12500000000000000000 5000791987093187 5000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000791987093187/5000000000000000 : ℝ)) (X := (12508116821537397207/12500000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13751267689434571/100000000000000000000 : ℝ) ≤ ((92469989541817529/92500000000000000 : ℝ)+2*(152171105303/88800000000000 : ℝ)*(357/3125 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (92469989541817529/92500000000000000 : ℝ)+2*(152171105303/88800000000000 : ℝ)*(357/3125 : ℝ)=(2500167736888639/2500000000000000 : ℝ) by norm_num, show 1+2*(13751267689434571/100000000000000000000 : ℝ)=(50013751267689434571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8116821537397207/25000000000000000000 : ℝ)+(13751267689434571/100000000000000000000 : ℝ) ≤ ((92469989541817529/92500000000000000 : ℝ)+(152171105303/88800000000000 : ℝ)*((1761/12500 : ℝ)+(357/3125 : ℝ)))^(4197/1024 : ℝ) := by
    rw [show (92469989541817529/92500000000000000 : ℝ)+(152171105303/88800000000000 : ℝ)*((1761/12500 : ℝ)+(357/3125 : ℝ))=(2000225492174093/2000000000000000 : ℝ) by norm_num, show 1+(8116821537397207/25000000000000000000 : ℝ)+(13751267689434571/100000000000000000000 : ℝ)=(100046218553839023399/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8116821537397207/25000000000000000000 : ℝ) ≤ ((92469989541817529/92500000000000000 : ℝ)+2*(152171105303/88800000000000 : ℝ)*(1761/12500 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (92469989541817529/92500000000000000 : ℝ)+2*(152171105303/88800000000000 : ℝ)*(1761/12500 : ℝ)=(5000791987093187/5000000000000000 : ℝ) by norm_num, show 1+2*(8116821537397207/25000000000000000000 : ℝ)=(12508116821537397207/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92469989541817529/92500000000000000 : ℝ)*(X 1 0+X 2 0)+(152171105303/88800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (92469989541817529/92500000000000000 : ℝ)) (alpha := (152171105303/88800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92469989541817529/92500000000000000 : ℝ)*(X 0 1+X 2 1)+(152171105303/88800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (92469989541817529/92500000000000000 : ℝ)) (alpha := (152171105303/88800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92469989541817529/92500000000000000 : ℝ)*(X 0 2+X 1 2)+(152171105303/88800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (92469989541817529/92500000000000000 : ℝ)) (alpha := (152171105303/88800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2138520433/10000000000 : ℝ)*X 0 0+(2695971723/5000000000 : ℝ)*X 0 1+(105333043/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672253917/5000000000 : ℝ)*X 1 0+(-2202055977/10000000000 : ℝ)*X 1 1+(263332619/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336126973/2500000000 : ℝ)*X 2 0+(2633326307/5000000000 : ℝ)*X 2 1+(-2202055589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435628853/1000000000 : ℝ)*X 0 0+(4231978741/10000000000 : ℝ)*X 0 1+(896835831/2000000000 : ℝ)*X 0 2+(435628853/1000000000 : ℝ)*X 1 0+(4231978741/10000000000 : ℝ)*X 1 1+(896835831/2000000000 : ℝ)*X 1 2+(435628853/1000000000 : ℝ)*X 2 0+(4231978741/10000000000 : ℝ)*X 2 1+(896835831/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1069262473/5000000000 : ℝ)*X 0 0+(329185487/625000000 : ℝ)*X 0 1+(1078325367/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062525523/2000000000 : ℝ)*X 1 0+(-415416127/2000000000 : ℝ)*X 1 1+(539162701/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312627417/10000000000 : ℝ)*X 2 0+(5391627163/10000000000 : ℝ)*X 2 1+(-259635087/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871259599/2000000000 : ℝ)*X 0 0+(4483544261/10000000000 : ℝ)*X 0 1+(2116308011/5000000000 : ℝ)*X 0 2+(871259599/2000000000 : ℝ)*X 1 0+(4483544261/10000000000 : ℝ)*X 1 1+(2116308011/5000000000 : ℝ)*X 1 2+(871259599/2000000000 : ℝ)*X 2 0+(4483544261/10000000000 : ℝ)*X 2 1+(2116308011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1850011871771746037583/185000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62198253/5000000000000 : ℝ)*(base19) + (1087335241/100000000000000 : ℝ)*(base23) + (208988219/100000000000000 : ℝ)*(upper3) + (130003399/100000000000000 : ℝ)*(upper4) + (85214897/12500000000000 : ℝ)*(upper5) + (93332728665571/1562500000000 : ℝ)*(major0) + (93332728665571/1562500000000 : ℝ)*(major1) + (93332728665571/1562500000000 : ℝ)*(major2) + (7981416512064739/100000000000000 : ℝ)*(sp0) + (798146034901381/10000000000000 : ℝ)*(sp1) + (7981460505643629/100000000000000 : ℝ)*(sp2) + (3965117838299369/100000000000000 : ℝ)*(sp3) + (45080914131/100000000000000 : ℝ)*(sp4) + (9504579369/100000000000000 : ℝ)*(sp7) + (1982563671439369/50000000000000 : ℝ)*(f.failure) + (798146159297887/10000000000000 : ℝ)*(f.sum) + (571664560861/138750000000000000000000000 : ℝ)*base65 + (4849741932307177/433593750000000000000000000000 : ℝ)*base67 + (1236380464192823/433593750000000000000000000000 : ℝ)*base70 + (20359282180931833/1734375000000000000000000000000 : ℝ)*base71 + (123548563429/34687500000000000000000000 : ℝ)*base73 + (13325210710181833/1734375000000000000000000000000 : ℝ)*base75 + (3940755484818167/1734375000000000000000000000000 : ℝ)*base78 + (215899510934903/27099609375000000000000000000 : ℝ)*base80 + (281563496543/69375000000000000000000000 : ℝ)*base81 + (516233/125000000000000000000 : ℝ)*base90 + (516233/125000000000000000000 : ℝ)*base92 + (516233/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319000700184329482153677/144531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (471319997/50000000000000 : ℝ)*(base19) + (35272909/5000000000000 : ℝ)*(base23) + (6967721/20000000000000 : ℝ)*(upper2) + (109668717/50000000000000 : ℝ)*(upper3) + (133323197/100000000000000 : ℝ)*(upper5) + (750442208749659/12500000000000 : ℝ)*(major0) + (750442208749659/12500000000000 : ℝ)*(major1) + (750442208749659/12500000000000 : ℝ)*(major2) + (14220846289/50000000000000 : ℝ)*(sp1) + (27810541433/100000000000000 : ℝ)*(sp2) + (4010936160698053/50000000000000 : ℝ)*(sp4) + (8021842937063533/100000000000000 : ℝ)*(sp5) + (2005460951349123/25000000000000 : ℝ)*(sp6) + (797040589005419/20000000000000 : ℝ)*(sp7) + (797040589005419/20000000000000 : ℝ)*(f.failure) + (4010936160698053/50000000000000 : ℝ)*(f.sum) + (489092177753/92500000000000000000000000 : ℝ)*base66 + (295063255515671/72265625000000000000000000000 : ℝ)*base67 + (8075720230265257/578125000000000000000000000000 : ℝ)*base70 + (3733365245297243/578125000000000000000000000000 : ℝ)*base71 + (570336201731/185000000000000000000000000 : ℝ)*base74 + (3443064386827757/578125000000000000000000000000 : ℝ)*base76 + (344758396577941/289062500000000000000000000000 : ℝ)*base78 + (2965091149202941/289062500000000000000000000000 : ℝ)*base80 + (560054882163/92500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (271083/50000000000000000000 : ℝ)*base90 + (271083/50000000000000000000 : ℝ)*base92 + (271083/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1202_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1202_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1202_s8_0 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85540937/400000000 : ℝ)*x 0 + (673986977/1250000000 : ℝ)*x 1 + (5266697907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85540937/400000000 : ℝ)^8395 ≤ (6500256263483/50000000000000 : ℝ)^6347 := by
    have hnat : (85540937 : ℕ)^8395*50000000000000^6347 ≤ 6500256263483^6347*400000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85540937 400000000 6500256263483 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673986977/1250000000 : ℝ)^8395 ≤ (22087774131961/50000000000000 : ℝ)^6347 := by
    have hnat : (673986977 : ℕ)^8395*50000000000000^6347 ≤ 22087774131961^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673986977 1250000000 22087774131961 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266697907/10000000000 : ℝ)^8395 ≤ (42823939204997/100000000000000 : ℝ)^6347 := by
    have hnat : (5266697907 : ℕ)^8395*100000000000000^6347 ≤ 42823939204997^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266697907 10000000000 42823939204997 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85540937/400000000 : ℝ), (673986977/1250000000 : ℝ), (5266697907/10000000000 : ℝ)] ![(6500256263483/50000000000000 : ℝ), (22087774131961/50000000000000 : ℝ), (42823939204997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85540937/400000000 : ℝ)|^8395 ≤ (6500256263483/50000000000000 : ℝ)^6347
        have hw : |(-85540937/400000000 : ℝ)|=(85540937/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673986977/1250000000 : ℝ)|^8395 ≤ (22087774131961/50000000000000 : ℝ)^6347
        have hw : |(673986977/1250000000 : ℝ)|=(673986977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266697907/10000000000 : ℝ)|^8395 ≤ (42823939204997/100000000000000 : ℝ)^6347
        have hw : |(5266697907/10000000000 : ℝ)|=(5266697907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s8_1 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672248241/5000000000 : ℝ)*x 0 + (-2202010791/10000000000 : ℝ)*x 1 + (526669789/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672248241/5000000000 : ℝ)^8395 ≤ (43662631043129/100000000000000 : ℝ)^6347 := by
    have hnat : (2672248241 : ℕ)^8395*100000000000000^6347 ≤ 43662631043129^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672248241 5000000000 43662631043129 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202010791/10000000000 : ℝ)^8395 ≤ (6756714959267/50000000000000 : ℝ)^6347 := by
    have hnat : (2202010791 : ℕ)^8395*50000000000000^6347 ≤ 6756714959267^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202010791 10000000000 6756714959267 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526669789/1000000000 : ℝ)^8395 ≤ (21411969511083/50000000000000 : ℝ)^6347 := by
    have hnat : (526669789 : ℕ)^8395*50000000000000^6347 ≤ 21411969511083^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526669789 1000000000 21411969511083 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672248241/5000000000 : ℝ), (-2202010791/10000000000 : ℝ), (526669789/1000000000 : ℝ)] ![(43662631043129/100000000000000 : ℝ), (6756714959267/50000000000000 : ℝ), (21411969511083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672248241/5000000000 : ℝ)|^8395 ≤ (43662631043129/100000000000000 : ℝ)^6347
        have hw : |(2672248241/5000000000 : ℝ)|=(2672248241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202010791/10000000000 : ℝ)|^8395 ≤ (6756714959267/50000000000000 : ℝ)^6347
        have hw : |(-2202010791/10000000000 : ℝ)|=(2202010791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526669789/1000000000 : ℝ)|^8395 ≤ (21411969511083/50000000000000 : ℝ)^6347
        have hw : |(526669789/1000000000 : ℝ)|=(526669789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s8_2 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334031031/625000000 : ℝ)*x 0 + (5266697859/10000000000 : ℝ)*x 1 + (-2202010813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334031031/625000000 : ℝ)^8395 ≤ (4366263119441/10000000000000 : ℝ)^6347 := by
    have hnat : (334031031 : ℕ)^8395*10000000000000^6347 ≤ 4366263119441^6347*625000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334031031 625000000 4366263119441 10000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266697859/10000000000 : ℝ)^8395 ≤ (42823938688769/100000000000000 : ℝ)^6347 := by
    have hnat : (5266697859 : ℕ)^8395*100000000000000^6347 ≤ 42823938688769^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266697859 10000000000 42823938688769 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202010813/10000000000 : ℝ)^8395 ≤ (13513430097109/100000000000000 : ℝ)^6347 := by
    have hnat : (2202010813 : ℕ)^8395*100000000000000^6347 ≤ 13513430097109^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202010813 10000000000 13513430097109 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334031031/625000000 : ℝ), (5266697859/10000000000 : ℝ), (-2202010813/10000000000 : ℝ)] ![(4366263119441/10000000000000 : ℝ), (42823938688769/100000000000000 : ℝ), (13513430097109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334031031/625000000 : ℝ)|^8395 ≤ (4366263119441/10000000000000 : ℝ)^6347
        have hw : |(334031031/625000000 : ℝ)|=(334031031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266697859/10000000000 : ℝ)|^8395 ≤ (42823938688769/100000000000000 : ℝ)^6347
        have hw : |(5266697859/10000000000 : ℝ)|=(5266697859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202010813/10000000000 : ℝ)|^8395 ≤ (13513430097109/100000000000000 : ℝ)^6347
        have hw : |(-2202010813/10000000000 : ℝ)|=(2202010813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s8_3 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356290543/10000000000 : ℝ)*x 0 + (846414481/2000000000 : ℝ)*x 1 + (4484085229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356290543/10000000000 : ℝ)^8395 ≤ (3331730764879/10000000000000 : ℝ)^6347 := by
    have hnat : (4356290543 : ℕ)^8395*10000000000000^6347 ≤ 3331730764879^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356290543 10000000000 3331730764879 10000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846414481/2000000000 : ℝ)^8395 ≤ (8016636437649/25000000000000 : ℝ)^6347 := by
    have hnat : (846414481 : ℕ)^8395*25000000000000^6347 ≤ 8016636437649^6347*2000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846414481 2000000000 8016636437649 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484085229/10000000000 : ℝ)^8395 ≤ (17308073289147/50000000000000 : ℝ)^6347 := by
    have hnat : (4484085229 : ℕ)^8395*50000000000000^6347 ≤ 17308073289147^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484085229 10000000000 17308073289147 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356290543/10000000000 : ℝ), (846414481/2000000000 : ℝ), (4484085229/10000000000 : ℝ)] ![(3331730764879/10000000000000 : ℝ), (8016636437649/25000000000000 : ℝ), (17308073289147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356290543/10000000000 : ℝ)|^8395 ≤ (3331730764879/10000000000000 : ℝ)^6347
        have hw : |(4356290543/10000000000 : ℝ)|=(4356290543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846414481/2000000000 : ℝ)|^8395 ≤ (8016636437649/25000000000000 : ℝ)^6347
        have hw : |(846414481/2000000000 : ℝ)|=(846414481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484085229/10000000000 : ℝ)|^8395 ≤ (17308073289147/50000000000000 : ℝ)^6347
        have hw : |(4484085229/10000000000 : ℝ)|=(4484085229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s8_4 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267316011/1250000000 : ℝ)*x 0 + (5267013643/10000000000 : ℝ)*x 1 + (5391578997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267316011/1250000000 : ℝ)^8395 ≤ (6500275010589/50000000000000 : ℝ)^6347 := by
    have hnat : (267316011 : ℕ)^8395*50000000000000^6347 ≤ 6500275010589^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267316011 1250000000 6500275010589 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267013643/10000000000 : ℝ)^8395 ≤ (1713093396011/4000000000000 : ℝ)^6347 := by
    have hnat : (5267013643 : ℕ)^8395*4000000000000^6347 ≤ 1713093396011^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267013643 10000000000 1713093396011 4000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391578997/10000000000 : ℝ)^8395 ≤ (22086057529367/50000000000000 : ℝ)^6347 := by
    have hnat : (5391578997 : ℕ)^8395*50000000000000^6347 ≤ 22086057529367^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391578997 10000000000 22086057529367 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267316011/1250000000 : ℝ), (5267013643/10000000000 : ℝ), (5391578997/10000000000 : ℝ)] ![(6500275010589/50000000000000 : ℝ), (1713093396011/4000000000000 : ℝ), (22086057529367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267316011/1250000000 : ℝ)|^8395 ≤ (6500275010589/50000000000000 : ℝ)^6347
        have hw : |(-267316011/1250000000 : ℝ)|=(267316011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267013643/10000000000 : ℝ)|^8395 ≤ (1713093396011/4000000000000 : ℝ)^6347
        have hw : |(5267013643/10000000000 : ℝ)|=(5267013643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391578997/10000000000 : ℝ)|^8395 ≤ (22086057529367/50000000000000 : ℝ)^6347
        have hw : |(5391578997/10000000000 : ℝ)|=(5391578997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s8_5 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328159709/2500000000 : ℝ)*x 0 + (-259641107/1250000000 : ℝ)*x 1 + (1347895099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328159709/2500000000 : ℝ)^8395 ≤ (4331871648037/10000000000000 : ℝ)^6347 := by
    have hnat : (1328159709 : ℕ)^8395*10000000000000^6347 ≤ 4331871648037^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328159709 2500000000 4331871648037 10000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259641107/1250000000 : ℝ)^8395 ≤ (12509153280779/100000000000000 : ℝ)^6347 := by
    have hnat : (259641107 : ℕ)^8395*100000000000000^6347 ≤ 12509153280779^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259641107 1250000000 12509153280779 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347895099/2500000000 : ℝ)^8395 ≤ (44172130218837/100000000000000 : ℝ)^6347 := by
    have hnat : (1347895099 : ℕ)^8395*100000000000000^6347 ≤ 44172130218837^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347895099 2500000000 44172130218837 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328159709/2500000000 : ℝ), (-259641107/1250000000 : ℝ), (1347895099/2500000000 : ℝ)] ![(4331871648037/10000000000000 : ℝ), (12509153280779/100000000000000 : ℝ), (44172130218837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328159709/2500000000 : ℝ)|^8395 ≤ (4331871648037/10000000000000 : ℝ)^6347
        have hw : |(1328159709/2500000000 : ℝ)|=(1328159709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259641107/1250000000 : ℝ)|^8395 ≤ (12509153280779/100000000000000 : ℝ)^6347
        have hw : |(-259641107/1250000000 : ℝ)|=(259641107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347895099/2500000000 : ℝ)|^8395 ≤ (44172130218837/100000000000000 : ℝ)^6347
        have hw : |(1347895099/2500000000 : ℝ)|=(1347895099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s8_6 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312639657/10000000000 : ℝ)*x 0 + (673947417/1250000000 : ℝ)*x 1 + (-2077129187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312639657/10000000000 : ℝ)^8395 ≤ (43318725334801/100000000000000 : ℝ)^6347 := by
    have hnat : (5312639657 : ℕ)^8395*100000000000000^6347 ≤ 43318725334801^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312639657 10000000000 43318725334801 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673947417/1250000000 : ℝ)^8395 ≤ (44172118732269/100000000000000 : ℝ)^6347 := by
    have hnat : (673947417 : ℕ)^8395*100000000000000^6347 ≤ 44172118732269^6347*1250000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673947417 1250000000 44172118732269 100000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077129187/10000000000 : ℝ)^8395 ≤ (6254577958691/50000000000000 : ℝ)^6347 := by
    have hnat : (2077129187 : ℕ)^8395*50000000000000^6347 ≤ 6254577958691^6347*10000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077129187 10000000000 6254577958691 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312639657/10000000000 : ℝ), (673947417/1250000000 : ℝ), (-2077129187/10000000000 : ℝ)] ![(43318725334801/100000000000000 : ℝ), (44172118732269/100000000000000 : ℝ), (6254577958691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312639657/10000000000 : ℝ)|^8395 ≤ (43318725334801/100000000000000 : ℝ)^6347
        have hw : |(5312639657/10000000000 : ℝ)|=(5312639657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673947417/1250000000 : ℝ)|^8395 ≤ (44172118732269/100000000000000 : ℝ)^6347
        have hw : |(673947417/1250000000 : ℝ)|=(673947417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077129187/10000000000 : ℝ)|^8395 ≤ (6254577958691/50000000000000 : ℝ)^6347
        have hw : |(-2077129187/10000000000 : ℝ)|=(2077129187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1202_s8_7 (p : ℝ) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435629979/1000000000 : ℝ)*x 0 + (1120862867/2500000000 : ℝ)*x 1 + (2116354371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435629979/1000000000 : ℝ)^8395 ≤ (8329350297677/25000000000000 : ℝ)^6347 := by
    have hnat : (435629979 : ℕ)^8395*25000000000000^6347 ≤ 8329350297677^6347*1000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435629979 1000000000 8329350297677 25000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120862867/2500000000 : ℝ)^8395 ≤ (6921935111869/20000000000000 : ℝ)^6347 := by
    have hnat : (1120862867 : ℕ)^8395*20000000000000^6347 ≤ 6921935111869^6347*2500000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120862867 2500000000 6921935111869 20000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116354371/5000000000 : ℝ)^8395 ≤ (16036461614551/50000000000000 : ℝ)^6347 := by
    have hnat : (2116354371 : ℕ)^8395*50000000000000^6347 ≤ 16036461614551^6347*5000000000^8395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116354371 5000000000 16036461614551 50000000000000 8395 6347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8395/2048 : ℝ)) 8395 6347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435629979/1000000000 : ℝ), (1120862867/2500000000 : ℝ), (2116354371/5000000000 : ℝ)] ![(8329350297677/25000000000000 : ℝ), (6921935111869/20000000000000 : ℝ), (16036461614551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435629979/1000000000 : ℝ)|^8395 ≤ (8329350297677/25000000000000 : ℝ)^6347
        have hw : |(435629979/1000000000 : ℝ)|=(435629979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120862867/2500000000 : ℝ)|^8395 ≤ (6921935111869/20000000000000 : ℝ)^6347
        have hw : |(1120862867/2500000000 : ℝ)|=(1120862867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116354371/5000000000 : ℝ)|^8395 ≤ (16036461614551/50000000000000 : ℝ)^6347
        have hw : |(2116354371/5000000000 : ℝ)|=(2116354371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1202_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1143/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11429/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11429/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11429/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11429/100000 : ℝ) ^ (4197/1024 : ℝ) ≤ (1721994050025821/12500000000000000000 : ℝ) := by
    have hpowers : (11429/100000 : ℝ)^4197 ≤ (1721994050025821/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11429 : ℕ)^4197*12500000000000000000^1024 ≤ 1721994050025821^1024*100000^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11429 100000 1721994050025821 12500000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11429/100000 : ℝ)) (X := (1721994050025821/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (4197/1024 : ℝ) ≤ (32420083448578623/100000000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^4197 ≤ (32420083448578623/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14083 : ℕ)^4197*100000000000000000000^1024 ≤ 32420083448578623^1024*100000^4197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 32420083448578623 100000000000000000000 4197 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (32420083448578623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251721994050025821/6250000000000000000 : ℝ) ≤ (10000672151837837/10000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (6251721994050025821/6250000000000000000 : ℝ)^1024 ≤ (10000672151837837/10000000000000000 : ℝ)^4197 := by
      have hnat : (6251721994050025821 : ℕ)^1024*10000000000000000^4197 ≤ 10000672151837837^4197*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251721994050025821 6250000000000000000 10000672151837837 10000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000672151837837/10000000000000000 : ℝ)) (X := (6251721994050025821/6250000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046196035848785191/100000000000000000000 : ℝ) ≤ (2000225382331967/2000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (100046196035848785191/100000000000000000000 : ℝ)^1024 ≤ (2000225382331967/2000000000000000 : ℝ)^4197 := by
      have hnat : (100046196035848785191 : ℕ)^1024*2000000000000000^4197 ≤ 2000225382331967^4197*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046196035848785191 100000000000000000000 2000225382331967 2000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000225382331967/2000000000000000 : ℝ)) (X := (100046196035848785191/100000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032420083448578623/50000000000000000000 : ℝ) ≤ (10001581671481833/10000000000000000 : ℝ) ^ (4197/1024 : ℝ) := by
    have hpowers : (50032420083448578623/50000000000000000000 : ℝ)^1024 ≤ (10001581671481833/10000000000000000 : ℝ)^4197 := by
      have hnat : (50032420083448578623 : ℕ)^1024*10000000000000000^4197 ≤ 10001581671481833^4197*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032420083448578623 50000000000000000000 10001581671481833 10000000000000000 1024 4197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001581671481833/10000000000000000 : ℝ)) (X := (50032420083448578623/50000000000000000000 : ℝ)) (by norm_num) 4197 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1721994050025821/12500000000000000000 : ℝ) ≤ ((13265694495483194557/13270000000000000000 : ℝ)+2*(227379910999/132700000000000 : ℝ)*(11429/100000 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (13265694495483194557/13270000000000000000 : ℝ)+2*(227379910999/132700000000000 : ℝ)*(11429/100000 : ℝ)=(10000672151837837/10000000000000000 : ℝ) by norm_num, show 1+2*(1721994050025821/12500000000000000000 : ℝ)=(6251721994050025821/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32420083448578623/100000000000000000000 : ℝ)+(1721994050025821/12500000000000000000 : ℝ) ≤ ((13265694495483194557/13270000000000000000 : ℝ)+(227379910999/132700000000000 : ℝ)*((14083/100000 : ℝ)+(11429/100000 : ℝ)))^(4197/1024 : ℝ) := by
    rw [show (13265694495483194557/13270000000000000000 : ℝ)+(227379910999/132700000000000 : ℝ)*((14083/100000 : ℝ)+(11429/100000 : ℝ))=(2000225382331967/2000000000000000 : ℝ) by norm_num, show 1+(32420083448578623/100000000000000000000 : ℝ)+(1721994050025821/12500000000000000000 : ℝ)=(100046196035848785191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32420083448578623/100000000000000000000 : ℝ) ≤ ((13265694495483194557/13270000000000000000 : ℝ)+2*(227379910999/132700000000000 : ℝ)*(14083/100000 : ℝ))^(4197/1024 : ℝ) := by
    rw [show (13265694495483194557/13270000000000000000 : ℝ)+2*(227379910999/132700000000000 : ℝ)*(14083/100000 : ℝ)=(10001581671481833/10000000000000000 : ℝ) by norm_num, show 1+2*(32420083448578623/100000000000000000000 : ℝ)=(50032420083448578623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13265694495483194557/13270000000000000000 : ℝ)*(X 1 0+X 2 0)+(227379910999/132700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (11429/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (13265694495483194557/13270000000000000000 : ℝ)) (alpha := (227379910999/132700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13265694495483194557/13270000000000000000 : ℝ)*(X 0 1+X 2 1)+(227379910999/132700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (11429/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (13265694495483194557/13270000000000000000 : ℝ)) (alpha := (227379910999/132700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13265694495483194557/13270000000000000000 : ℝ)*(X 0 2+X 1 2)+(227379910999/132700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4197/1024 : ℝ)) (lo := (11429/100000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (13265694495483194557/13270000000000000000 : ℝ)) (alpha := (227379910999/132700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85540937/400000000 : ℝ)*X 0 0+(673986977/1250000000 : ℝ)*X 0 1+(5266697907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672248241/5000000000 : ℝ)*X 1 0+(-2202010791/10000000000 : ℝ)*X 1 1+(526669789/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334031031/625000000 : ℝ)*X 2 0+(5266697859/10000000000 : ℝ)*X 2 1+(-2202010813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356290543/10000000000 : ℝ)*X 0 0+(846414481/2000000000 : ℝ)*X 0 1+(4484085229/10000000000 : ℝ)*X 0 2+(4356290543/10000000000 : ℝ)*X 1 0+(846414481/2000000000 : ℝ)*X 1 1+(4484085229/10000000000 : ℝ)*X 1 2+(4356290543/10000000000 : ℝ)*X 2 0+(846414481/2000000000 : ℝ)*X 2 1+(4484085229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267316011/1250000000 : ℝ)*X 0 0+(5267013643/10000000000 : ℝ)*X 0 1+(5391578997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328159709/2500000000 : ℝ)*X 1 0+(-259641107/1250000000 : ℝ)*X 1 1+(1347895099/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312639657/10000000000 : ℝ)*X 2 0+(673947417/1250000000 : ℝ)*X 2 1+(-2077129187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435629979/1000000000 : ℝ)*X 0 0+(1120862867/2500000000 : ℝ)*X 0 1+(2116354371/5000000000 : ℝ)*X 0 2+(435629979/1000000000 : ℝ)*X 1 0+(1120862867/2500000000 : ℝ)*X 1 1+(2116354371/5000000000 : ℝ)*X 1 2+(435629979/1000000000 : ℝ)*X 2 0+(1120862867/2500000000 : ℝ)*X 2 1+(2116354371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1202_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5403370442031177080125203213/663500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321861267/20000000000000 : ℝ)*(base19) + (758105989/50000000000000 : ℝ)*(base23) + (60936661/100000000000000 : ℝ)*(lower2) + (2766319/1250000000000 : ℝ)*(upper3) + (13124037/12500000000000 : ℝ)*(upper5) + (5977770153358203/100000000000000 : ℝ)*(major0) + (5977770153358203/100000000000000 : ℝ)*(major1) + (5977770153358203/100000000000000 : ℝ)*(major2) + (7987399614229417/100000000000000 : ℝ)*(sp0) + (998430024123323/12500000000000 : ℝ)*(sp1) + (7987440286080941/100000000000000 : ℝ)*(sp2) + (3968073521129297/100000000000000 : ℝ)*(sp3) + (42188063501/100000000000000 : ℝ)*(sp4) + (4942367247/20000000000000 : ℝ)*(sp7) + (992024558241383/25000000000000 : ℝ)*(f.failure) + (7987441802292919/100000000000000 : ℝ)*(f.sum) + (298273975717/6635000000000000000000000000 : ℝ)*base65 + (14367473094080601071/1327000000000000000000000000000000 : ℝ)*base67 + (4476966502932398929/1327000000000000000000000000000000 : ℝ)*base70 + (20596848036697601071/1327000000000000000000000000000000 : ℝ)*base71 + (16340710902481/3317500000000000000000000000 : ℝ)*base73 + (18709690464320398929/1327000000000000000000000000000000 : ℝ)*base76 + (2606656287398398929/1327000000000000000000000000000000 : ℝ)*base78 + (12652425712527398929/1327000000000000000000000000000000 : ℝ)*base80 + (38894576422453/6635000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (20769/62500000000000000000 : ℝ)*base89 + (20769/62500000000000000000 : ℝ)*base91 + (20769/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1611965419043006830588473591/331750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6453779/12500000000000 : ℝ)*(base15) + (56346051/10000000000000 : ℝ)*(lower1) + (121911297/50000000000000 : ℝ)*(lower2) + (6307073/25000000000000 : ℝ)*(upper3) + (65459571/25000000000000 : ℝ)*(upper4) + (6008043258588479/100000000000000 : ℝ)*(major0) + (6008043258588479/100000000000000 : ℝ)*(major1) + (6008043258588479/100000000000000 : ℝ)*(major2) + (40564249011/100000000000000 : ℝ)*(sp1) + (1698789741/6250000000000 : ℝ)*(sp3) + (1605578511894129/20000000000000 : ℝ)*(sp4) + (4013925971795701/50000000000000 : ℝ)*(sp5) + (1605578511894129/20000000000000 : ℝ)*(sp6) + (49852082688807/1250000000000 : ℝ)*(sp7) + (15578882014611/390625000000 : ℝ)*(f.failure) + (1605578511894129/20000000000000 : ℝ)*(f.sum) + (32567116316959/6635000000000000000000000000 : ℝ)*base66 + (9293423783742808803/1327000000000000000000000000000000 : ℝ)*base67 + (85506191892464808803/1327000000000000000000000000000000 : ℝ)*base69 + (4412180005706191197/1327000000000000000000000000000000 : ℝ)*base72 + (520988651807/207343750000000000000000000 : ℝ)*base74 + (14504262129605808803/1327000000000000000000000000000000 : ℝ)*base75 + (19855994148436808803/1327000000000000000000000000000000 : ℝ)*base77 + (3179162489647808803/1327000000000000000000000000000000 : ℝ)*base79 + (202529972093303/3317500000000000000000000000 : ℝ)*base81 + (1109/7812500000000000000 : ℝ)*base89 + (1109/7812500000000000000 : ℝ)*base91 + (1109/7812500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1202_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1202_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1202_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1202_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1202_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1202_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4197/1024 : ℝ) ≤ p) (hpb : p ≤ (8395/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3766143/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1202_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
