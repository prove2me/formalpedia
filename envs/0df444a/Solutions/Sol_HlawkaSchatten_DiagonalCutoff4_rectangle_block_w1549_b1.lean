-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1549_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:29.541691+00:00
-- url     : https://prove2.me/submissions/790156b6-c7b4-4a36-967a-41ebec84c0d2

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
theorem support_rectangle_w1549_s3_0 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1814389013/10000000000 : ℝ)*x 0 + (5430600381/10000000000 : ℝ)*x 1 + (521736913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1814389013/10000000000 : ℝ)^4595 ≤ (5560810385657/50000000000000 : ℝ)^3571 := by
    have hnat : (1814389013 : ℕ)^4595*50000000000000^3571 ≤ 5560810385657^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814389013 10000000000 5560810385657 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430600381/10000000000 : ℝ)^4595 ≤ (22792097832237/50000000000000 : ℝ)^3571 := by
    have hnat : (5430600381 : ℕ)^4595*50000000000000^3571 ≤ 22792097832237^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430600381 10000000000 22792097832237 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521736913/1000000000 : ℝ)^4595 ≤ (5411772944341/12500000000000 : ℝ)^3571 := by
    have hnat : (521736913 : ℕ)^4595*12500000000000^3571 ≤ 5411772944341^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521736913 1000000000 5411772944341 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1814389013/10000000000 : ℝ), (5430600381/10000000000 : ℝ), (521736913/1000000000 : ℝ)] ![(5560810385657/50000000000000 : ℝ), (22792097832237/50000000000000 : ℝ), (5411772944341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1814389013/10000000000 : ℝ)|^4595 ≤ (5560810385657/50000000000000 : ℝ)^3571
        have hw : |(-1814389013/10000000000 : ℝ)|=(1814389013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430600381/10000000000 : ℝ)|^4595 ≤ (22792097832237/50000000000000 : ℝ)^3571
        have hw : |(5430600381/10000000000 : ℝ)|=(5430600381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521736913/1000000000 : ℝ)|^4595 ≤ (5411772944341/12500000000000 : ℝ)^3571
        have hw : |(521736913/1000000000 : ℝ)|=(521736913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s3_1 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337505971/2500000000 : ℝ)*x 0 + (-1923565783/10000000000 : ℝ)*x 1 + (1304342273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337505971/2500000000 : ℝ)^4595 ≤ (22357875323787/50000000000000 : ℝ)^3571 := by
    have hnat : (1337505971 : ℕ)^4595*50000000000000^3571 ≤ 22357875323787^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337505971 2500000000 22357875323787 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1923565783/10000000000 : ℝ)^4595 ≤ (11990066180577/100000000000000 : ℝ)^3571 := by
    have hnat : (1923565783 : ℕ)^4595*100000000000000^3571 ≤ 11990066180577^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923565783 10000000000 11990066180577 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304342273/2500000000 : ℝ)^4595 ≤ (43294183148979/100000000000000 : ℝ)^3571 := by
    have hnat : (1304342273 : ℕ)^4595*100000000000000^3571 ≤ 43294183148979^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304342273 2500000000 43294183148979 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337505971/2500000000 : ℝ), (-1923565783/10000000000 : ℝ), (1304342273/2500000000 : ℝ)] ![(22357875323787/50000000000000 : ℝ), (11990066180577/100000000000000 : ℝ), (43294183148979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337505971/2500000000 : ℝ)|^4595 ≤ (22357875323787/50000000000000 : ℝ)^3571
        have hw : |(1337505971/2500000000 : ℝ)|=(1337505971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1923565783/10000000000 : ℝ)|^4595 ≤ (11990066180577/100000000000000 : ℝ)^3571
        have hw : |(-1923565783/10000000000 : ℝ)|=(1923565783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304342273/2500000000 : ℝ)|^4595 ≤ (43294183148979/100000000000000 : ℝ)^3571
        have hw : |(1304342273/2500000000 : ℝ)|=(1304342273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s3_2 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350023907/10000000000 : ℝ)*x 0 + (208694763/400000000 : ℝ)*x 1 + (-120222861/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350023907/10000000000 : ℝ)^4595 ≤ (44715750894933/100000000000000 : ℝ)^3571 := by
    have hnat : (5350023907 : ℕ)^4595*100000000000000^3571 ≤ 44715750894933^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350023907 10000000000 44715750894933 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208694763/400000000 : ℝ)^4595 ≤ (2164709148373/5000000000000 : ℝ)^3571 := by
    have hnat : (208694763 : ℕ)^4595*5000000000000^3571 ≤ 2164709148373^3571*400000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208694763 400000000 2164709148373 5000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120222861/625000000 : ℝ)^4595 ≤ (749379132777/6250000000000 : ℝ)^3571 := by
    have hnat : (120222861 : ℕ)^4595*6250000000000^3571 ≤ 749379132777^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120222861 625000000 749379132777 6250000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350023907/10000000000 : ℝ), (208694763/400000000 : ℝ), (-120222861/625000000 : ℝ)] ![(44715750894933/100000000000000 : ℝ), (2164709148373/5000000000000 : ℝ), (749379132777/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350023907/10000000000 : ℝ)|^4595 ≤ (44715750894933/100000000000000 : ℝ)^3571
        have hw : |(5350023907/10000000000 : ℝ)|=(5350023907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208694763/400000000 : ℝ)|^4595 ≤ (2164709148373/5000000000000 : ℝ)^3571
        have hw : |(208694763/400000000 : ℝ)|=(208694763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120222861/625000000 : ℝ)|^4595 ≤ (749379132777/6250000000000 : ℝ)^3571
        have hw : |(-120222861/625000000 : ℝ)|=(120222861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s3_3 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265790309/625000000 : ℝ)*x 0 + (4010527847/10000000000 : ℝ)*x 1 + (4506680703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265790309/625000000 : ℝ)^4595 ≤ (33279400244359/100000000000000 : ℝ)^3571 := by
    have hnat : (265790309 : ℕ)^4595*100000000000000^3571 ≤ 33279400244359^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265790309 625000000 33279400244359 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010527847/10000000000 : ℝ)^4595 ≤ (30861556551757/100000000000000 : ℝ)^3571 := by
    have hnat : (4010527847 : ℕ)^4595*100000000000000^3571 ≤ 30861556551757^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010527847 10000000000 30861556551757 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506680703/10000000000 : ℝ)^4595 ≤ (35859043185143/100000000000000 : ℝ)^3571 := by
    have hnat : (4506680703 : ℕ)^4595*100000000000000^3571 ≤ 35859043185143^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506680703 10000000000 35859043185143 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265790309/625000000 : ℝ), (4010527847/10000000000 : ℝ), (4506680703/10000000000 : ℝ)] ![(33279400244359/100000000000000 : ℝ), (30861556551757/100000000000000 : ℝ), (35859043185143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265790309/625000000 : ℝ)|^4595 ≤ (33279400244359/100000000000000 : ℝ)^3571
        have hw : |(265790309/625000000 : ℝ)|=(265790309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010527847/10000000000 : ℝ)|^4595 ≤ (30861556551757/100000000000000 : ℝ)^3571
        have hw : |(4010527847/10000000000 : ℝ)|=(4010527847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506680703/10000000000 : ℝ)|^4595 ≤ (35859043185143/100000000000000 : ℝ)^3571
        have hw : |(4506680703/10000000000 : ℝ)|=(4506680703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s3_4 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9072091/50000000 : ℝ)*x 0 + (5218496251/10000000000 : ℝ)*x 1 + (21717859/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9072091/50000000 : ℝ)^4595 ≤ (1112185098111/10000000000000 : ℝ)^3571 := by
    have hnat : (9072091 : ℕ)^4595*10000000000000^3571 ≤ 1112185098111^3571*50000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9072091 50000000 1112185098111 10000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218496251/10000000000 : ℝ)^4595 ≤ (4330621887489/10000000000000 : ℝ)^3571 := by
    have hnat : (5218496251 : ℕ)^4595*10000000000000^3571 ≤ 4330621887489^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218496251 10000000000 4330621887489 10000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21717859/40000000 : ℝ)^4595 ≤ (22785965067041/50000000000000 : ℝ)^3571 := by
    have hnat : (21717859 : ℕ)^4595*50000000000000^3571 ≤ 22785965067041^3571*40000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21717859 40000000 22785965067041 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9072091/50000000 : ℝ), (5218496251/10000000000 : ℝ), (21717859/40000000 : ℝ)] ![(1112185098111/10000000000000 : ℝ), (4330621887489/10000000000000 : ℝ), (22785965067041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9072091/50000000 : ℝ)|^4595 ≤ (1112185098111/10000000000000 : ℝ)^3571
        have hw : |(-9072091/50000000 : ℝ)|=(9072091/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218496251/10000000000 : ℝ)|^4595 ≤ (4330621887489/10000000000000 : ℝ)^3571
        have hw : |(5218496251/10000000000 : ℝ)|=(5218496251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21717859/40000000 : ℝ)|^4595 ≤ (22785965067041/50000000000000 : ℝ)^3571
        have hw : |(21717859/40000000 : ℝ)|=(21717859/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s3_5 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293755883/10000000000 : ℝ)*x 0 + (-855735059/5000000000 : ℝ)*x 1 + (1085892957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293755883/10000000000 : ℝ)^4595 ≤ (44111516977017/100000000000000 : ℝ)^3571 := by
    have hnat : (5293755883 : ℕ)^4595*100000000000000^3571 ≤ 44111516977017^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293755883 10000000000 44111516977017 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855735059/5000000000 : ℝ)^4595 ≤ (10316552493391/100000000000000 : ℝ)^3571 := by
    have hnat : (855735059 : ℕ)^4595*100000000000000^3571 ≤ 10316552493391^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855735059 5000000000 10316552493391 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085892957/2000000000 : ℝ)^4595 ≤ (45571930512093/100000000000000 : ℝ)^3571 := by
    have hnat : (1085892957 : ℕ)^4595*100000000000000^3571 ≤ 45571930512093^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085892957 2000000000 45571930512093 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293755883/10000000000 : ℝ), (-855735059/5000000000 : ℝ), (1085892957/2000000000 : ℝ)] ![(44111516977017/100000000000000 : ℝ), (10316552493391/100000000000000 : ℝ), (45571930512093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293755883/10000000000 : ℝ)|^4595 ≤ (44111516977017/100000000000000 : ℝ)^3571
        have hw : |(5293755883/10000000000 : ℝ)|=(5293755883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855735059/5000000000 : ℝ)|^4595 ≤ (10316552493391/100000000000000 : ℝ)^3571
        have hw : |(-855735059/5000000000 : ℝ)|=(855735059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085892957/2000000000 : ℝ)|^4595 ≤ (45571930512093/100000000000000 : ℝ)^3571
        have hw : |(1085892957/2000000000 : ℝ)|=(1085892957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s3_6 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293755873/10000000000 : ℝ)*x 0 + (5429464779/10000000000 : ℝ)*x 1 + (-85573507/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293755873/10000000000 : ℝ)^4595 ≤ (8822303373959/20000000000000 : ℝ)^3571 := by
    have hnat : (5293755873 : ℕ)^4595*20000000000000^3571 ≤ 8822303373959^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293755873 10000000000 8822303373959 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429464779/10000000000 : ℝ)^4595 ≤ (45571930447291/100000000000000 : ℝ)^3571 := by
    have hnat : (5429464779 : ℕ)^4595*100000000000000^3571 ≤ 45571930447291^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429464779 10000000000 45571930447291 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85573507/500000000 : ℝ)^4595 ≤ (322392270751/3125000000000 : ℝ)^3571 := by
    have hnat : (85573507 : ℕ)^4595*3125000000000^3571 ≤ 322392270751^3571*500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85573507 500000000 322392270751 3125000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293755873/10000000000 : ℝ), (5429464779/10000000000 : ℝ), (-85573507/500000000 : ℝ)] ![(8822303373959/20000000000000 : ℝ), (45571930447291/100000000000000 : ℝ), (322392270751/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293755873/10000000000 : ℝ)|^4595 ≤ (8822303373959/20000000000000 : ℝ)^3571
        have hw : |(5293755873/10000000000 : ℝ)|=(5293755873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429464779/10000000000 : ℝ)|^4595 ≤ (45571930447291/100000000000000 : ℝ)^3571
        have hw : |(5429464779/10000000000 : ℝ)|=(5429464779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85573507/500000000 : ℝ)|^4595 ≤ (322392270751/3125000000000 : ℝ)^3571
        have hw : |(-85573507/500000000 : ℝ)|=(85573507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s3_7 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265794549/625000000 : ℝ)*x 0 + (4504058051/10000000000 : ℝ)*x 1 + (802634047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265794549/625000000 : ℝ)^4595 ≤ (33280083367291/100000000000000 : ℝ)^3571 := by
    have hnat : (265794549 : ℕ)^4595*100000000000000^3571 ≤ 33280083367291^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265794549 625000000 33280083367291 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504058051/10000000000 : ℝ)^4595 ≤ (17916096663427/50000000000000 : ℝ)^3571 := by
    have hnat : (4504058051 : ℕ)^4595*50000000000000^3571 ≤ 17916096663427^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504058051 10000000000 17916096663427 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802634047/2000000000 : ℝ)^4595 ≤ (6177544657663/20000000000000 : ℝ)^3571 := by
    have hnat : (802634047 : ℕ)^4595*20000000000000^3571 ≤ 6177544657663^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802634047 2000000000 6177544657663 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265794549/625000000 : ℝ), (4504058051/10000000000 : ℝ), (802634047/2000000000 : ℝ)] ![(33280083367291/100000000000000 : ℝ), (17916096663427/50000000000000 : ℝ), (6177544657663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265794549/625000000 : ℝ)|^4595 ≤ (33280083367291/100000000000000 : ℝ)^3571
        have hw : |(265794549/625000000 : ℝ)|=(265794549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504058051/10000000000 : ℝ)|^4595 ≤ (17916096663427/50000000000000 : ℝ)^3571
        have hw : |(4504058051/10000000000 : ℝ)|=(4504058051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802634047/2000000000 : ℝ)|^4595 ≤ (6177544657663/20000000000000 : ℝ)^3571
        have hw : |(802634047/2000000000 : ℝ)|=(802634047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1549_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1101/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15529/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15871/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2139/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15871/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2139/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15871/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2139/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15871/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2139/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15871/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2139/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15871/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2139/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2139/20000 : ℝ) ^ (4593/1024 : ℝ) ≤ (4421142719204527/100000000000000000000 : ℝ) := by
    have hpowers : (2139/20000 : ℝ)^4593 ≤ (4421142719204527/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2139 : ℕ)^4593*100000000000000000000^1024 ≤ 4421142719204527^1024*20000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2139 20000 4421142719204527 100000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2139/20000 : ℝ)) (X := (4421142719204527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15871/100000 : ℝ) ^ (4593/1024 : ℝ) ≤ (25967444403864309/100000000000000000000 : ℝ) := by
    have hpowers : (15871/100000 : ℝ)^4593 ≤ (25967444403864309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15871 : ℕ)^4593*100000000000000000000^1024 ≤ 25967444403864309^1024*100000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15871 100000 25967444403864309 100000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15871/100000 : ℝ)) (X := (25967444403864309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004421142719204527/50000000000000000000 : ℝ) ≤ (5000098565090809/5000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (50004421142719204527/50000000000000000000 : ℝ)^1024 ≤ (5000098565090809/5000000000000000 : ℝ)^4593 := by
      have hnat : (50004421142719204527 : ℕ)^1024*5000000000000000^4593 ≤ 5000098565090809^4593*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004421142719204527 50000000000000000000 5000098565090809 5000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000098565090809/5000000000000000 : ℝ)) (X := (50004421142719204527/50000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007597146780767209/25000000000000000000 : ℝ) ≤ (2000135485477287/2000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (25007597146780767209/25000000000000000000 : ℝ)^1024 ≤ (2000135485477287/2000000000000000 : ℝ)^4593 := by
      have hnat : (25007597146780767209 : ℕ)^1024*2000000000000000^4593 ≤ 2000135485477287^4593*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007597146780767209 25000000000000000000 2000135485477287 2000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000135485477287/2000000000000000 : ℝ)) (X := (25007597146780767209/25000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025967444403864309/50000000000000000000 : ℝ) ≤ (2500289431147813/2500000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (50025967444403864309/50000000000000000000 : ℝ)^1024 ≤ (2500289431147813/2500000000000000 : ℝ)^4593 := by
      have hnat : (50025967444403864309 : ℕ)^1024*2500000000000000^4593 ≤ 2500289431147813^4593*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025967444403864309 50000000000000000000 2500289431147813 2500000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500289431147813/2500000000000000 : ℝ)) (X := (50025967444403864309/50000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4421142719204527/100000000000000000000 : ℝ) ≤ ((25875373394304509569/25880000000000000000 : ℝ)+2*(480297204817/517600000000000 : ℝ)*(2139/20000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (25875373394304509569/25880000000000000000 : ℝ)+2*(480297204817/517600000000000 : ℝ)*(2139/20000 : ℝ)=(5000098565090809/5000000000000000 : ℝ) by norm_num, show 1+2*(4421142719204527/100000000000000000000 : ℝ)=(50004421142719204527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25967444403864309/100000000000000000000 : ℝ)+(4421142719204527/100000000000000000000 : ℝ) ≤ ((25875373394304509569/25880000000000000000 : ℝ)+(480297204817/517600000000000 : ℝ)*((15871/100000 : ℝ)+(2139/20000 : ℝ)))^(4593/1024 : ℝ) := by
    rw [show (25875373394304509569/25880000000000000000 : ℝ)+(480297204817/517600000000000 : ℝ)*((15871/100000 : ℝ)+(2139/20000 : ℝ))=(2000135485477287/2000000000000000 : ℝ) by norm_num, show 1+(25967444403864309/100000000000000000000 : ℝ)+(4421142719204527/100000000000000000000 : ℝ)=(25007597146780767209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25967444403864309/100000000000000000000 : ℝ) ≤ ((25875373394304509569/25880000000000000000 : ℝ)+2*(480297204817/517600000000000 : ℝ)*(15871/100000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (25875373394304509569/25880000000000000000 : ℝ)+2*(480297204817/517600000000000 : ℝ)*(15871/100000 : ℝ)=(2500289431147813/2500000000000000 : ℝ) by norm_num, show 1+2*(25967444403864309/100000000000000000000 : ℝ)=(50025967444403864309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25875373394304509569/25880000000000000000 : ℝ)*(X 1 0+X 2 0)+(480297204817/517600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (2139/20000 : ℝ)) (hi := (15871/100000 : ℝ)) (c := (25875373394304509569/25880000000000000000 : ℝ)) (alpha := (480297204817/517600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25875373394304509569/25880000000000000000 : ℝ)*(X 0 1+X 2 1)+(480297204817/517600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (2139/20000 : ℝ)) (hi := (15871/100000 : ℝ)) (c := (25875373394304509569/25880000000000000000 : ℝ)) (alpha := (480297204817/517600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25875373394304509569/25880000000000000000 : ℝ)*(X 0 2+X 1 2)+(480297204817/517600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (2139/20000 : ℝ)) (hi := (15871/100000 : ℝ)) (c := (25875373394304509569/25880000000000000000 : ℝ)) (alpha := (480297204817/517600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1814389013/10000000000 : ℝ)*X 0 0+(5430600381/10000000000 : ℝ)*X 0 1+(521736913/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337505971/2500000000 : ℝ)*X 1 0+(-1923565783/10000000000 : ℝ)*X 1 1+(1304342273/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350023907/10000000000 : ℝ)*X 2 0+(208694763/400000000 : ℝ)*X 2 1+(-120222861/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((265790309/625000000 : ℝ)*X 0 0+(4010527847/10000000000 : ℝ)*X 0 1+(4506680703/10000000000 : ℝ)*X 0 2+(265790309/625000000 : ℝ)*X 1 0+(4010527847/10000000000 : ℝ)*X 1 1+(4506680703/10000000000 : ℝ)*X 1 2+(265790309/625000000 : ℝ)*X 2 0+(4010527847/10000000000 : ℝ)*X 2 1+(4506680703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9072091/50000000 : ℝ)*X 0 0+(5218496251/10000000000 : ℝ)*X 0 1+(21717859/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293755883/10000000000 : ℝ)*X 1 0+(-855735059/5000000000 : ℝ)*X 1 1+(1085892957/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293755873/10000000000 : ℝ)*X 2 0+(5429464779/10000000000 : ℝ)*X 2 1+(-85573507/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265794549/625000000 : ℝ)*X 0 0+(4504058051/10000000000 : ℝ)*X 0 1+(802634047/2000000000 : ℝ)*X 0 2+(265794549/625000000 : ℝ)*X 1 0+(4504058051/10000000000 : ℝ)*X 1 1+(802634047/2000000000 : ℝ)*X 1 2+(265794549/625000000 : ℝ)*X 2 0+(4504058051/10000000000 : ℝ)*X 2 1+(802634047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (743074785530804037903409287/129400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256976847/25000000000000 : ℝ)*(base19) + (496667403/50000000000000 : ℝ)*(base23) + (29282897/100000000000000 : ℝ)*(lower2) + (26882873/20000000000000 : ℝ)*(upper3) + (3281361/3125000000000 : ℝ)*(upper5) + (335264914290353/10000000000000 : ℝ)*(major0) + (335264914290353/10000000000000 : ℝ)*(major1) + (335264914290353/10000000000000 : ℝ)*(major2) + (4689760155022783/100000000000000 : ℝ)*(sp0) + (586221891017067/12500000000000 : ℝ)*(sp1) + (2344887581354559/50000000000000 : ℝ)*(sp2) + (2015514616992057/100000000000000 : ℝ)*(sp3) + (8000510571/50000000000000 : ℝ)*(sp4) + (366067781/5000000000000 : ℝ)*(sp7) + (2015521938347677/100000000000000 : ℝ)*(f.failure) + (1172444039010981/25000000000000 : ℝ)*(f.sum) + (14049126486709/2588000000000000000000000000 : ℝ)*base65 + (2220621238449737857/258800000000000000000000000000000 : ℝ)*base67 + (4787751066137857/258800000000000000000000000000000 : ℝ)*base69 + (1484890403787337857/258800000000000000000000000000000 : ℝ)*base71 + (11291167604333/2588000000000000000000000000 : ℝ)*base73 + (1164803879772537857/258800000000000000000000000000000 : ℝ)*base75 + (1957495901109737857/258800000000000000000000000000000 : ℝ)*base77 + (2388451256611737857/258800000000000000000000000000000 : ℝ)*base79 + (1965968482963/2588000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (11585989/5000000000000000000000 : ℝ)*base90 + (11585989/5000000000000000000000 : ℝ)*base92 + (11585989/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (364561047072306169389970269/161750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78268091/20000000000000 : ℝ)*(base19) + (196819183/50000000000000 : ℝ)*(base23) + (6784733/100000000000000 : ℝ)*(upper2) + (60492349/100000000000000 : ℝ)*(upper3) + (52574307/100000000000000 : ℝ)*(upper5) + (423573070695589/12500000000000 : ℝ)*(major0) + (423573070695589/12500000000000 : ℝ)*(major1) + (423573070695589/12500000000000 : ℝ)*(major2) + (397701783/6250000000000 : ℝ)*(sp1) + (6216030883/100000000000000 : ℝ)*(sp2) + (4740043714001319/100000000000000 : ℝ)*(sp4) + (4740036959432337/100000000000000 : ℝ)*(sp5) + (474003710433207/10000000000000 : ℝ)*(sp6) + (2037125341999597/100000000000000 : ℝ)*(sp7) + (2037125341999597/100000000000000 : ℝ)*(f.failure) + (4740043714001319/100000000000000 : ℝ)*(f.sum) + (8933613720067/3235000000000000000000000000 : ℝ)*base66 + (887063567978758859/323500000000000000000000000000000 : ℝ)*base68 + (1699611467360258859/323500000000000000000000000000000 : ℝ)*base70 + (1823317487571258859/323500000000000000000000000000000 : ℝ)*base72 + (4994274125409/1617500000000000000000000000 : ℝ)*base73 + (5480551319628758859/323500000000000000000000000000000 : ℝ)*base76 + (1668269006169258859/323500000000000000000000000000000 : ℝ)*base78 + (4505006914899758859/323500000000000000000000000000000 : ℝ)*base80 + (12516001753/12636718750000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (11809429/5000000000000000000000 : ℝ)*base90 + (11809429/5000000000000000000000 : ℝ)*base92 + (11809429/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1549_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15529/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1549_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1549_s4_0 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18146763/100000000 : ℝ)*x 0 + (339292947/625000000 : ℝ)*x 1 + (2609546031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18146763/100000000 : ℝ)^4595 ≤ (2224777353499/20000000000000 : ℝ)^3571 := by
    have hnat : (18146763 : ℕ)^4595*20000000000000^3571 ≤ 2224777353499^3571*100000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18146763 100000000 2224777353499 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339292947/625000000 : ℝ)^4595 ≤ (22781766004999/50000000000000 : ℝ)^3571 := by
    have hnat : (339292947 : ℕ)^4595*50000000000000^3571 ≤ 22781766004999^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339292947 625000000 22781766004999 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609546031/5000000000 : ℝ)^4595 ≤ (43312581204759/100000000000000 : ℝ)^3571 := by
    have hnat : (2609546031 : ℕ)^4595*100000000000000^3571 ≤ 43312581204759^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609546031 5000000000 43312581204759 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18146763/100000000 : ℝ), (339292947/625000000 : ℝ), (2609546031/5000000000 : ℝ)] ![(2224777353499/20000000000000 : ℝ), (22781766004999/50000000000000 : ℝ), (43312581204759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18146763/100000000 : ℝ)|^4595 ≤ (2224777353499/20000000000000 : ℝ)^3571
        have hw : |(-18146763/100000000 : ℝ)|=(18146763/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339292947/625000000 : ℝ)|^4595 ≤ (22781766004999/50000000000000 : ℝ)^3571
        have hw : |(339292947/625000000 : ℝ)|=(339292947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609546031/5000000000 : ℝ)|^4595 ≤ (43312581204759/100000000000000 : ℝ)^3571
        have hw : |(2609546031/5000000000 : ℝ)|=(2609546031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s4_1 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349519197/10000000000 : ℝ)*x 0 + (-1921948501/10000000000 : ℝ)*x 1 + (5219092041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349519197/10000000000 : ℝ)^4595 ≤ (11177580734147/25000000000000 : ℝ)^3571 := by
    have hnat : (5349519197 : ℕ)^4595*25000000000000^3571 ≤ 11177580734147^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349519197 10000000000 11177580734147 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1921948501/10000000000 : ℝ)^4595 ≤ (11977096072683/100000000000000 : ℝ)^3571 := by
    have hnat : (1921948501 : ℕ)^4595*100000000000000^3571 ≤ 11977096072683^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921948501 10000000000 11977096072683 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219092041/10000000000 : ℝ)^4595 ≤ (43312580980509/100000000000000 : ℝ)^3571 := by
    have hnat : (5219092041 : ℕ)^4595*100000000000000^3571 ≤ 43312580980509^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219092041 10000000000 43312580980509 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349519197/10000000000 : ℝ), (-1921948501/10000000000 : ℝ), (5219092041/10000000000 : ℝ)] ![(11177580734147/25000000000000 : ℝ), (11977096072683/100000000000000 : ℝ), (43312580980509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349519197/10000000000 : ℝ)|^4595 ≤ (11177580734147/25000000000000 : ℝ)^3571
        have hw : |(5349519197/10000000000 : ℝ)|=(5349519197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1921948501/10000000000 : ℝ)|^4595 ≤ (11977096072683/100000000000000 : ℝ)^3571
        have hw : |(-1921948501/10000000000 : ℝ)|=(1921948501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219092041/10000000000 : ℝ)|^4595 ≤ (43312580980509/100000000000000 : ℝ)^3571
        have hw : |(5219092041/10000000000 : ℝ)|=(5219092041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s4_2 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674759601/5000000000 : ℝ)*x 0 + (2609546019/5000000000 : ℝ)*x 1 + (-1921948497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674759601/5000000000 : ℝ)^4595 ≤ (1117758074759/2500000000000 : ℝ)^3571 := by
    have hnat : (2674759601 : ℕ)^4595*2500000000000^3571 ≤ 1117758074759^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674759601 5000000000 1117758074759 2500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609546019/5000000000 : ℝ)^4595 ≤ (43312580948473/100000000000000 : ℝ)^3571 := by
    have hnat : (2609546019 : ℕ)^4595*100000000000000^3571 ≤ 43312580948473^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609546019 5000000000 43312580948473 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921948497/10000000000 : ℝ)^4595 ≤ (374284251269/3125000000000 : ℝ)^3571 := by
    have hnat : (1921948497 : ℕ)^4595*3125000000000^3571 ≤ 374284251269^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921948497 10000000000 374284251269 3125000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674759601/5000000000 : ℝ), (2609546019/5000000000 : ℝ), (-1921948497/10000000000 : ℝ)] ![(1117758074759/2500000000000 : ℝ), (43312580948473/100000000000000 : ℝ), (374284251269/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674759601/5000000000 : ℝ)|^4595 ≤ (1117758074759/2500000000000 : ℝ)^3571
        have hw : |(2674759601/5000000000 : ℝ)|=(2674759601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609546019/5000000000 : ℝ)|^4595 ≤ (43312580948473/100000000000000 : ℝ)^3571
        have hw : |(2609546019/5000000000 : ℝ)|=(2609546019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921948497/10000000000 : ℝ)|^4595 ≤ (374284251269/3125000000000 : ℝ)^3571
        have hw : |(-1921948497/10000000000 : ℝ)|=(1921948497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s4_3 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126412947/5000000000 : ℝ)*x 0 + (4014737839/10000000000 : ℝ)*x 1 + (4502430039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126412947/5000000000 : ℝ)^4595 ≤ (4160152793601/12500000000000 : ℝ)^3571 := by
    have hnat : (2126412947 : ℕ)^4595*12500000000000^3571 ≤ 4160152793601^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126412947 5000000000 4160152793601 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014737839/10000000000 : ℝ)^4595 ≤ (30903249112497/100000000000000 : ℝ)^3571 := by
    have hnat : (4014737839 : ℕ)^4595*100000000000000^3571 ≤ 30903249112497^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014737839 10000000000 30903249112497 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502430039/10000000000 : ℝ)^4595 ≤ (35815528524357/100000000000000 : ℝ)^3571 := by
    have hnat : (4502430039 : ℕ)^4595*100000000000000^3571 ≤ 35815528524357^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502430039 10000000000 35815528524357 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126412947/5000000000 : ℝ), (4014737839/10000000000 : ℝ), (4502430039/10000000000 : ℝ)] ![(4160152793601/12500000000000 : ℝ), (30903249112497/100000000000000 : ℝ), (35815528524357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126412947/5000000000 : ℝ)|^4595 ≤ (4160152793601/12500000000000 : ℝ)^3571
        have hw : |(2126412947/5000000000 : ℝ)|=(2126412947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4014737839/10000000000 : ℝ)|^4595 ≤ (30903249112497/100000000000000 : ℝ)^3571
        have hw : |(4014737839/10000000000 : ℝ)|=(4014737839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502430039/10000000000 : ℝ)|^4595 ≤ (35815528524357/100000000000000 : ℝ)^3571
        have hw : |(4502430039/10000000000 : ℝ)|=(4502430039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s4_4 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1814704177/10000000000 : ℝ)*x 0 + (2610090529/5000000000 : ℝ)*x 1 + (2713794979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1814704177/10000000000 : ℝ)^4595 ≤ (5562053327373/50000000000000 : ℝ)^3571 := by
    have hnat : (1814704177 : ℕ)^4595*50000000000000^3571 ≤ 5562053327373^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814704177 10000000000 5562053327373 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610090529/5000000000 : ℝ)^4595 ≤ (5415526314689/12500000000000 : ℝ)^3571 := by
    have hnat : (2610090529 : ℕ)^4595*12500000000000^3571 ≤ 5415526314689^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610090529 5000000000 5415526314689 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713794979/5000000000 : ℝ)^4595 ≤ (45551682808857/100000000000000 : ℝ)^3571 := by
    have hnat : (2713794979 : ℕ)^4595*100000000000000^3571 ≤ 45551682808857^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713794979 5000000000 45551682808857 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1814704177/10000000000 : ℝ), (2610090529/5000000000 : ℝ), (2713794979/5000000000 : ℝ)] ![(5562053327373/50000000000000 : ℝ), (5415526314689/12500000000000 : ℝ), (45551682808857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1814704177/10000000000 : ℝ)|^4595 ≤ (5562053327373/50000000000000 : ℝ)^3571
        have hw : |(-1814704177/10000000000 : ℝ)|=(1814704177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610090529/5000000000 : ℝ)|^4595 ≤ (5415526314689/12500000000000 : ℝ)^3571
        have hw : |(2610090529/5000000000 : ℝ)|=(2610090529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713794979/5000000000 : ℝ)|^4595 ≤ (45551682808857/100000000000000 : ℝ)^3571
        have hw : |(2713794979/5000000000 : ℝ)|=(2713794979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s4_5 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647105913/5000000000 : ℝ)*x 0 + (-428362587/2500000000 : ℝ)*x 1 + (5427589671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647105913/5000000000 : ℝ)^4595 ≤ (5514550718459/12500000000000 : ℝ)^3571 := by
    have hnat : (2647105913 : ℕ)^4595*12500000000000^3571 ≤ 5514550718459^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647105913 5000000000 5514550718459 12500000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428362587/2500000000 : ℝ)^4595 ≤ (10331914522831/100000000000000 : ℝ)^3571 := by
    have hnat : (428362587 : ℕ)^4595*100000000000000^3571 ≤ 10331914522831^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428362587 2500000000 10331914522831 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427589671/10000000000 : ℝ)^4595 ≤ (11387919927369/25000000000000 : ℝ)^3571 := by
    have hnat : (5427589671 : ℕ)^4595*25000000000000^3571 ≤ 11387919927369^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427589671 10000000000 11387919927369 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647105913/5000000000 : ℝ), (-428362587/2500000000 : ℝ), (5427589671/10000000000 : ℝ)] ![(5514550718459/12500000000000 : ℝ), (10331914522831/100000000000000 : ℝ), (11387919927369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647105913/5000000000 : ℝ)|^4595 ≤ (5514550718459/12500000000000 : ℝ)^3571
        have hw : |(2647105913/5000000000 : ℝ)|=(2647105913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428362587/2500000000 : ℝ)|^4595 ≤ (10331914522831/100000000000000 : ℝ)^3571
        have hw : |(-428362587/2500000000 : ℝ)|=(428362587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427589671/10000000000 : ℝ)|^4595 ≤ (11387919927369/25000000000000 : ℝ)^3571
        have hw : |(5427589671/10000000000 : ℝ)|=(5427589671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s4_6 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323552903/2500000000 : ℝ)*x 0 + (5427589643/10000000000 : ℝ)*x 1 + (-428362671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323552903/2500000000 : ℝ)^4595 ≤ (8823280690613/20000000000000 : ℝ)^3571 := by
    have hnat : (1323552903 : ℕ)^4595*20000000000000^3571 ≤ 8823280690613^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323552903 2500000000 8823280690613 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427589643/10000000000 : ℝ)^4595 ≤ (22775839703549/50000000000000 : ℝ)^3571 := by
    have hnat : (5427589643 : ℕ)^4595*50000000000000^3571 ≤ 22775839703549^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427589643 10000000000 22775839703549 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428362671/2500000000 : ℝ)^4595 ≤ (206638342597/2000000000000 : ℝ)^3571 := by
    have hnat : (428362671 : ℕ)^4595*2000000000000^3571 ≤ 206638342597^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428362671 2500000000 206638342597 2000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323552903/2500000000 : ℝ), (5427589643/10000000000 : ℝ), (-428362671/2500000000 : ℝ)] ![(8823280690613/20000000000000 : ℝ), (22775839703549/50000000000000 : ℝ), (206638342597/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323552903/2500000000 : ℝ)|^4595 ≤ (8823280690613/20000000000000 : ℝ)^3571
        have hw : |(1323552903/2500000000 : ℝ)|=(1323552903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427589643/10000000000 : ℝ)|^4595 ≤ (22775839703549/50000000000000 : ℝ)^3571
        have hw : |(5427589643/10000000000 : ℝ)|=(5427589643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428362671/2500000000 : ℝ)|^4595 ≤ (206638342597/2000000000000 : ℝ)^3571
        have hw : |(-428362671/2500000000 : ℝ)|=(428362671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s4_7 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170115607/400000000 : ℝ)*x 0 + (4499895831/10000000000 : ℝ)*x 1 + (1004322737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170115607/400000000 : ℝ)^4595 ≤ (33281869641787/100000000000000 : ℝ)^3571 := by
    have hnat : (170115607 : ℕ)^4595*100000000000000^3571 ≤ 33281869641787^3571*400000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170115607 400000000 33281869641787 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499895831/10000000000 : ℝ)^4595 ≤ (35789591075341/100000000000000 : ℝ)^3571 := by
    have hnat : (4499895831 : ℕ)^4595*100000000000000^3571 ≤ 35789591075341^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499895831 10000000000 35789591075341 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004322737/2500000000 : ℝ)^4595 ≤ (30928539271749/100000000000000 : ℝ)^3571 := by
    have hnat : (1004322737 : ℕ)^4595*100000000000000^3571 ≤ 30928539271749^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004322737 2500000000 30928539271749 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170115607/400000000 : ℝ), (4499895831/10000000000 : ℝ), (1004322737/2500000000 : ℝ)] ![(33281869641787/100000000000000 : ℝ), (35789591075341/100000000000000 : ℝ), (30928539271749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170115607/400000000 : ℝ)|^4595 ≤ (33281869641787/100000000000000 : ℝ)^3571
        have hw : |(170115607/400000000 : ℝ)|=(170115607/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499895831/10000000000 : ℝ)|^4595 ≤ (35789591075341/100000000000000 : ℝ)^3571
        have hw : |(4499895831/10000000000 : ℝ)|=(4499895831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004322737/2500000000 : ℝ)|^4595 ≤ (30928539271749/100000000000000 : ℝ)^3571
        have hw : |(1004322737/2500000000 : ℝ)|=(1004322737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1549_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11047/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1101/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1101/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1101/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1101/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1101/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1101/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1101/10000 : ℝ) ^ (4593/1024 : ℝ) ≤ (201437000187241/4000000000000000000 : ℝ) := by
    have hpowers : (1101/10000 : ℝ)^4593 ≤ (201437000187241/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1101 : ℕ)^4593*4000000000000000000^1024 ≤ 201437000187241^1024*10000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1101 10000 201437000187241 4000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1101/10000 : ℝ)) (X := (201437000187241/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15529/100000 : ℝ) ^ (4593/1024 : ℝ) ≤ (23550177718722097/100000000000000000000 : ℝ) := by
    have hpowers : (15529/100000 : ℝ)^4593 ≤ (23550177718722097/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15529 : ℕ)^4593*100000000000000000000^1024 ≤ 23550177718722097^1024*100000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15529 100000 23550177718722097 100000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15529/100000 : ℝ)) (X := (23550177718722097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000201437000187241/2000000000000000000 : ℝ) ≤ (125002806763239/125000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (2000201437000187241/2000000000000000000 : ℝ)^1024 ≤ (125002806763239/125000000000000 : ℝ)^4593 := by
      have hnat : (2000201437000187241 : ℕ)^1024*125000000000000^4593 ≤ 125002806763239^4593*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000201437000187241 2000000000000000000 125002806763239 125000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125002806763239/125000000000000 : ℝ)) (X := (2000201437000187241/2000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014293051361701561/50000000000000000000 : ℝ) ≤ (10000637250569169/10000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (50014293051361701561/50000000000000000000 : ℝ)^1024 ≤ (10000637250569169/10000000000000000 : ℝ)^4593 := by
      have hnat : (50014293051361701561 : ℕ)^1024*10000000000000000^4593 ≤ 10000637250569169^4593*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014293051361701561 50000000000000000000 10000637250569169 10000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000637250569169/10000000000000000 : ℝ)) (X := (50014293051361701561/50000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023550177718722097/50000000000000000000 : ℝ) ≤ (5000524980039609/5000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (50023550177718722097/50000000000000000000 : ℝ)^1024 ≤ (5000524980039609/5000000000000000 : ℝ)^4593 := by
      have hnat : (50023550177718722097 : ℕ)^1024*5000000000000000^4593 ≤ 5000524980039609^4593*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023550177718722097 50000000000000000000 5000524980039609 5000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000524980039609/5000000000000000 : ℝ)) (X := (50023550177718722097/50000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(201437000187241/4000000000000000000 : ℝ) ≤ ((451819268376348843/451900000000000000 : ℝ)+2*(412709510049/451900000000000 : ℝ)*(1101/10000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (451819268376348843/451900000000000000 : ℝ)+2*(412709510049/451900000000000 : ℝ)*(1101/10000 : ℝ)=(125002806763239/125000000000000 : ℝ) by norm_num, show 1+2*(201437000187241/4000000000000000000 : ℝ)=(2000201437000187241/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23550177718722097/100000000000000000000 : ℝ)+(201437000187241/4000000000000000000 : ℝ) ≤ ((451819268376348843/451900000000000000 : ℝ)+(412709510049/451900000000000 : ℝ)*((15529/100000 : ℝ)+(1101/10000 : ℝ)))^(4593/1024 : ℝ) := by
    rw [show (451819268376348843/451900000000000000 : ℝ)+(412709510049/451900000000000 : ℝ)*((15529/100000 : ℝ)+(1101/10000 : ℝ))=(10000637250569169/10000000000000000 : ℝ) by norm_num, show 1+(23550177718722097/100000000000000000000 : ℝ)+(201437000187241/4000000000000000000 : ℝ)=(50014293051361701561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23550177718722097/100000000000000000000 : ℝ) ≤ ((451819268376348843/451900000000000000 : ℝ)+2*(412709510049/451900000000000 : ℝ)*(15529/100000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (451819268376348843/451900000000000000 : ℝ)+2*(412709510049/451900000000000 : ℝ)*(15529/100000 : ℝ)=(5000524980039609/5000000000000000 : ℝ) by norm_num, show 1+2*(23550177718722097/100000000000000000000 : ℝ)=(50023550177718722097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (451819268376348843/451900000000000000 : ℝ)*(X 1 0+X 2 0)+(412709510049/451900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (15529/100000 : ℝ)) (c := (451819268376348843/451900000000000000 : ℝ)) (alpha := (412709510049/451900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (451819268376348843/451900000000000000 : ℝ)*(X 0 1+X 2 1)+(412709510049/451900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (15529/100000 : ℝ)) (c := (451819268376348843/451900000000000000 : ℝ)) (alpha := (412709510049/451900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (451819268376348843/451900000000000000 : ℝ)*(X 0 2+X 1 2)+(412709510049/451900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (15529/100000 : ℝ)) (c := (451819268376348843/451900000000000000 : ℝ)) (alpha := (412709510049/451900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-18146763/100000000 : ℝ)*X 0 0+(339292947/625000000 : ℝ)*X 0 1+(2609546031/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349519197/10000000000 : ℝ)*X 1 0+(-1921948501/10000000000 : ℝ)*X 1 1+(5219092041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674759601/5000000000 : ℝ)*X 2 0+(2609546019/5000000000 : ℝ)*X 2 1+(-1921948497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2126412947/5000000000 : ℝ)*X 0 0+(4014737839/10000000000 : ℝ)*X 0 1+(4502430039/10000000000 : ℝ)*X 0 2+(2126412947/5000000000 : ℝ)*X 1 0+(4014737839/10000000000 : ℝ)*X 1 1+(4502430039/10000000000 : ℝ)*X 1 2+(2126412947/5000000000 : ℝ)*X 2 0+(4014737839/10000000000 : ℝ)*X 2 1+(4502430039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1814704177/10000000000 : ℝ)*X 0 0+(2610090529/5000000000 : ℝ)*X 0 1+(2713794979/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647105913/5000000000 : ℝ)*X 1 0+(-428362587/2500000000 : ℝ)*X 1 1+(5427589671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323552903/2500000000 : ℝ)*X 2 0+(5427589643/10000000000 : ℝ)*X 2 1+(-428362671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170115607/400000000 : ℝ)*X 0 0+(4499895831/10000000000 : ℝ)*X 0 1+(1004322737/2500000000 : ℝ)*X 0 2+(170115607/400000000 : ℝ)*X 1 0+(4499895831/10000000000 : ℝ)*X 1 1+(1004322737/2500000000 : ℝ)*X 1 2+(170115607/400000000 : ℝ)*X 2 0+(4499895831/10000000000 : ℝ)*X 2 1+(1004322737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28133785317282086917694859/5648750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (417372637/50000000000000 : ℝ)*(base19) + (390811137/50000000000000 : ℝ)*(base23) + (6160763/20000000000000 : ℝ)*(lower2) + (59504649/50000000000000 : ℝ)*(upper3) + (81435491/100000000000000 : ℝ)*(upper5) + (852702008948007/25000000000000 : ℝ)*(major0) + (852702008948007/25000000000000 : ℝ)*(major1) + (852702008948007/25000000000000 : ℝ)*(major2) + (190844698489257/4000000000000 : ℝ)*(sp0) + (4771129579912251/100000000000000 : ℝ)*(sp1) + (4771129633035251/100000000000000 : ℝ)*(sp2) + (205047923215317/10000000000000 : ℝ)*(sp3) + (12952426101/100000000000000 : ℝ)*(sp4) + (6258755591/100000000000000 : ℝ)*(sp7) + (2050485490908761/100000000000000 : ℝ)*(f.failure) + (190845216586301/4000000000000 : ℝ)*(f.sum) + (236618963971/176523437500000000000000000 : ℝ)*base66 + (51299477389728599/11297500000000000000000000000000 : ℝ)*base68 + (27409996248836099/11297500000000000000000000000000 : ℝ)*base70 + (77563878761521099/11297500000000000000000000000000 : ℝ)*base72 + (3152322591093/5648750000000000000000000000 : ℝ)*base73 + (141778567536278599/11297500000000000000000000000000 : ℝ)*base76 + (150629412224883599/11297500000000000000000000000000 : ℝ)*base78 + (57335563081028599/11297500000000000000000000000000 : ℝ)*base80 + (39550638557527/22595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2420577/5000000000000000000000 : ℝ)*base90 + (2420577/5000000000000000000000 : ℝ)*base92 + (2420577/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124533351511978995634670817/11297500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2665339339/100000000000000 : ℝ)*(base19) + (1242776523/50000000000000 : ℝ)*(base23) + (2146311/4000000000000 : ℝ)*(upper2) + (227385561/100000000000000 : ℝ)*(upper3) + (70887601/25000000000000 : ℝ)*(upper5) + (1723370028635127/50000000000000 : ℝ)*(major0) + (1723370028635127/50000000000000 : ℝ)*(major1) + (1723370028635127/50000000000000 : ℝ)*(major2) + (40909001029/100000000000000 : ℝ)*(sp1) + (32652704133/100000000000000 : ℝ)*(sp2) + (602674112155333/12500000000000 : ℝ)*(sp4) + (602668665362787/12500000000000 : ℝ)*(sp5) + (2410678879492743/50000000000000 : ℝ)*(sp6) + (259010856232691/12500000000000 : ℝ)*(sp7) + (259010856232691/12500000000000 : ℝ)*(f.failure) + (602674112155333/12500000000000 : ℝ)*(f.sum) + (52165205962697/11297500000000000000000000000 : ℝ)*base66 + (88348744420231061/22595000000000000000000000000000 : ℝ)*base67 + (160890706464511061/22595000000000000000000000000000 : ℝ)*base69 + (3236593288523939/22595000000000000000000000000000 : ℝ)*base72 + (10131932821999/22595000000000000000000000000 : ℝ)*base74 + (336884817836176061/22595000000000000000000000000000 : ℝ)*base75 + (29783890104478939/22595000000000000000000000000000 : ℝ)*base78 + (118430461196431061/22595000000000000000000000000000 : ℝ)*base79 + (41367612743141/22595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3859413/625000000000000000000 : ℝ)*base89 + (3859413/625000000000000000000 : ℝ)*base91 + (3859413/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1549_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1549_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1549_s5_0 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-907352861/5000000000 : ℝ)*x 0 + (5428482441/10000000000 : ℝ)*x 1 + (5219277363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907352861/5000000000 : ℝ)^4595 ≤ (11124118841373/100000000000000 : ℝ)^3571 := by
    have hnat : (907352861 : ℕ)^4595*100000000000000^3571 ≤ 11124118841373^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907352861 5000000000 11124118841373 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428482441/10000000000 : ℝ)^4595 ≤ (22780660585631/50000000000000 : ℝ)^3571 := by
    have hnat : (5428482441 : ℕ)^4595*50000000000000^3571 ≤ 22780660585631^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428482441 10000000000 22780660585631 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219277363/10000000000 : ℝ)^4595 ≤ (10828639993041/25000000000000 : ℝ)^3571 := by
    have hnat : (5219277363 : ℕ)^4595*25000000000000^3571 ≤ 10828639993041^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219277363 10000000000 10828639993041 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907352861/5000000000 : ℝ), (5428482441/10000000000 : ℝ), (5219277363/10000000000 : ℝ)] ![(11124118841373/100000000000000 : ℝ), (22780660585631/50000000000000 : ℝ), (10828639993041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907352861/5000000000 : ℝ)|^4595 ≤ (11124118841373/100000000000000 : ℝ)^3571
        have hw : |(-907352861/5000000000 : ℝ)|=(907352861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428482441/10000000000 : ℝ)|^4595 ≤ (22780660585631/50000000000000 : ℝ)^3571
        have hw : |(5428482441/10000000000 : ℝ)|=(5428482441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219277363/10000000000 : ℝ)|^4595 ≤ (10828639993041/25000000000000 : ℝ)^3571
        have hw : |(5219277363/10000000000 : ℝ)|=(5219277363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s5_1 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42795727/80000000 : ℝ)*x 0 + (-1921773391/10000000000 : ℝ)*x 1 + (5219277231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42795727/80000000 : ℝ)^4595 ≤ (22354874743971/50000000000000 : ℝ)^3571 := by
    have hnat : (42795727 : ℕ)^4595*50000000000000^3571 ≤ 22354874743971^3571*80000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42795727 80000000 22354874743971 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1921773391/10000000000 : ℝ)^4595 ≤ (11975691931663/100000000000000 : ℝ)^3571 := by
    have hnat : (1921773391 : ℕ)^4595*100000000000000^3571 ≤ 11975691931663^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921773391 10000000000 11975691931663 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219277231/10000000000 : ℝ)^4595 ≤ (43314558562573/100000000000000 : ℝ)^3571 := by
    have hnat : (5219277231 : ℕ)^4595*100000000000000^3571 ≤ 43314558562573^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219277231 10000000000 43314558562573 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42795727/80000000 : ℝ), (-1921773391/10000000000 : ℝ), (5219277231/10000000000 : ℝ)] ![(22354874743971/50000000000000 : ℝ), (11975691931663/100000000000000 : ℝ), (43314558562573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42795727/80000000 : ℝ)|^4595 ≤ (22354874743971/50000000000000 : ℝ)^3571
        have hw : |(42795727/80000000 : ℝ)|=(42795727/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1921773391/10000000000 : ℝ)|^4595 ≤ (11975691931663/100000000000000 : ℝ)^3571
        have hw : |(-1921773391/10000000000 : ℝ)|=(1921773391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219277231/10000000000 : ℝ)|^4595 ≤ (43314558562573/100000000000000 : ℝ)^3571
        have hw : |(5219277231/10000000000 : ℝ)|=(5219277231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s5_2 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349465919/10000000000 : ℝ)*x 0 + (2609638579/5000000000 : ℝ)*x 1 + (-192177343/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349465919/10000000000 : ℝ)^4595 ≤ (44709749961137/100000000000000 : ℝ)^3571 := by
    have hnat : (5349465919 : ℕ)^4595*100000000000000^3571 ≤ 44709749961137^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349465919 10000000000 44709749961137 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609638579/5000000000 : ℝ)^4595 ≤ (43314557783027/100000000000000 : ℝ)^3571 := by
    have hnat : (2609638579 : ℕ)^4595*100000000000000^3571 ≤ 43314557783027^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609638579 5000000000 43314557783027 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192177343/1000000000 : ℝ)^4595 ≤ (5987846122193/50000000000000 : ℝ)^3571 := by
    have hnat : (192177343 : ℕ)^4595*50000000000000^3571 ≤ 5987846122193^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192177343 1000000000 5987846122193 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349465919/10000000000 : ℝ), (2609638579/5000000000 : ℝ), (-192177343/1000000000 : ℝ)] ![(44709749961137/100000000000000 : ℝ), (43314557783027/100000000000000 : ℝ), (5987846122193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349465919/10000000000 : ℝ)|^4595 ≤ (44709749961137/100000000000000 : ℝ)^3571
        have hw : |(5349465919/10000000000 : ℝ)|=(5349465919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609638579/5000000000 : ℝ)|^4595 ≤ (43314557783027/100000000000000 : ℝ)^3571
        have hw : |(2609638579/5000000000 : ℝ)|=(2609638579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-192177343/1000000000 : ℝ)|^4595 ≤ (5987846122193/50000000000000 : ℝ)^3571
        have hw : |(-192177343/1000000000 : ℝ)|=(192177343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s5_3 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85056903/200000000 : ℝ)*x 0 + (2007594869/5000000000 : ℝ)*x 1 + (2250986899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85056903/200000000 : ℝ)^4595 ≤ (16640708125717/50000000000000 : ℝ)^3571 := by
    have hnat : (85056903 : ℕ)^4595*50000000000000^3571 ≤ 16640708125717^3571*200000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85056903 200000000 16640708125717 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007594869/5000000000 : ℝ)^4595 ≤ (15453862561031/50000000000000 : ℝ)^3571 := by
    have hnat : (2007594869 : ℕ)^4595*50000000000000^3571 ≤ 15453862561031^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007594869 5000000000 15453862561031 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250986899/5000000000 : ℝ)^4595 ≤ (17905429309617/50000000000000 : ℝ)^3571 := by
    have hnat : (2250986899 : ℕ)^4595*50000000000000^3571 ≤ 17905429309617^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250986899 5000000000 17905429309617 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85056903/200000000 : ℝ), (2007594869/5000000000 : ℝ), (2250986899/5000000000 : ℝ)] ![(16640708125717/50000000000000 : ℝ), (15453862561031/50000000000000 : ℝ), (17905429309617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85056903/200000000 : ℝ)|^4595 ≤ (16640708125717/50000000000000 : ℝ)^3571
        have hw : |(85056903/200000000 : ℝ)|=(85056903/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007594869/5000000000 : ℝ)|^4595 ≤ (15453862561031/50000000000000 : ℝ)^3571
        have hw : |(2007594869/5000000000 : ℝ)|=(2007594869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250986899/5000000000 : ℝ)|^4595 ≤ (17905429309617/50000000000000 : ℝ)^3571
        have hw : |(2250986899/5000000000 : ℝ)|=(2250986899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s5_4 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1814733307/10000000000 : ℝ)*x 0 + (2610181283/5000000000 : ℝ)*x 1 + (5427389189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1814733307/10000000000 : ℝ)^4595 ≤ (5562168213201/50000000000000 : ℝ)^3571 := by
    have hnat : (1814733307 : ℕ)^4595*50000000000000^3571 ≤ 5562168213201^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814733307 10000000000 5562168213201 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610181283/5000000000 : ℝ)^4595 ≤ (43326148896499/100000000000000 : ℝ)^3571 := by
    have hnat : (2610181283 : ℕ)^4595*100000000000000^3571 ≤ 43326148896499^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610181283 5000000000 43326148896499 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427389189/10000000000 : ℝ)^4595 ≤ (113873786671/250000000000 : ℝ)^3571 := by
    have hnat : (5427389189 : ℕ)^4595*250000000000^3571 ≤ 113873786671^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427389189 10000000000 113873786671 250000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1814733307/10000000000 : ℝ), (2610181283/5000000000 : ℝ), (5427389189/10000000000 : ℝ)] ![(5562168213201/50000000000000 : ℝ), (43326148896499/100000000000000 : ℝ), (113873786671/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1814733307/10000000000 : ℝ)|^4595 ≤ (5562168213201/50000000000000 : ℝ)^3571
        have hw : |(-1814733307/10000000000 : ℝ)|=(1814733307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610181283/5000000000 : ℝ)|^4595 ≤ (43326148896499/100000000000000 : ℝ)^3571
        have hw : |(2610181283/5000000000 : ℝ)|=(2610181283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427389189/10000000000 : ℝ)|^4595 ≤ (113873786671/250000000000 : ℝ)^3571
        have hw : |(5427389189/10000000000 : ℝ)|=(5427389189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s5_5 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323565123/2500000000 : ℝ)*x 0 + (-214207717/1250000000 : ℝ)*x 1 + (542738947/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323565123/2500000000 : ℝ)^4595 ≤ (8823385513529/20000000000000 : ℝ)^3571 := by
    have hnat : (1323565123 : ℕ)^4595*20000000000000^3571 ≤ 8823385513529^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323565123 2500000000 8823385513529 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214207717/1250000000 : ℝ)^4595 ≤ (10333554708291/100000000000000 : ℝ)^3571 := by
    have hnat : (214207717 : ℕ)^4595*100000000000000^3571 ≤ 10333554708291^3571*1250000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214207717 1250000000 10333554708291 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542738947/1000000000 : ℝ)^4595 ≤ (45549517702953/100000000000000 : ℝ)^3571 := by
    have hnat : (542738947 : ℕ)^4595*100000000000000^3571 ≤ 45549517702953^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542738947 1000000000 45549517702953 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323565123/2500000000 : ℝ), (-214207717/1250000000 : ℝ), (542738947/1000000000 : ℝ)] ![(8823385513529/20000000000000 : ℝ), (10333554708291/100000000000000 : ℝ), (45549517702953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323565123/2500000000 : ℝ)|^4595 ≤ (8823385513529/20000000000000 : ℝ)^3571
        have hw : |(1323565123/2500000000 : ℝ)|=(1323565123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214207717/1250000000 : ℝ)|^4595 ≤ (10333554708291/100000000000000 : ℝ)^3571
        have hw : |(-214207717/1250000000 : ℝ)|=(214207717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542738947/1000000000 : ℝ)|^4595 ≤ (45549517702953/100000000000000 : ℝ)^3571
        have hw : |(542738947/1000000000 : ℝ)|=(542738947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s5_6 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058852169/2000000000 : ℝ)*x 0 + (5427389329/10000000000 : ℝ)*x 1 + (-428415361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058852169/2000000000 : ℝ)^4595 ≤ (11029232838171/25000000000000 : ℝ)^3571 := by
    have hnat : (1058852169 : ℕ)^4595*25000000000000^3571 ≤ 11029232838171^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058852169 2000000000 11029232838171 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427389329/10000000000 : ℝ)^4595 ≤ (45549516180277/100000000000000 : ℝ)^3571 := by
    have hnat : (5427389329 : ℕ)^4595*100000000000000^3571 ≤ 45549516180277^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427389329 10000000000 45549516180277 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428415361/2500000000 : ℝ)^4595 ≤ (10333552442587/100000000000000 : ℝ)^3571 := by
    have hnat : (428415361 : ℕ)^4595*100000000000000^3571 ≤ 10333552442587^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428415361 2500000000 10333552442587 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058852169/2000000000 : ℝ), (5427389329/10000000000 : ℝ), (-428415361/2500000000 : ℝ)] ![(11029232838171/25000000000000 : ℝ), (45549516180277/100000000000000 : ℝ), (10333552442587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058852169/2000000000 : ℝ)|^4595 ≤ (11029232838171/25000000000000 : ℝ)^3571
        have hw : |(1058852169/2000000000 : ℝ)|=(1058852169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427389329/10000000000 : ℝ)|^4595 ≤ (45549516180277/100000000000000 : ℝ)^3571
        have hw : |(5427389329/10000000000 : ℝ)|=(5427389329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428415361/2500000000 : ℝ)|^4595 ≤ (10333552442587/100000000000000 : ℝ)^3571
        have hw : |(-428415361/2500000000 : ℝ)|=(428415361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_s5_7 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1063227309/2500000000 : ℝ)*x 0 + (11248623/25000000 : ℝ)*x 1 + (2008866479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063227309/2500000000 : ℝ)^4595 ≤ (33282061581647/100000000000000 : ℝ)^3571 := by
    have hnat : (1063227309 : ℕ)^4595*100000000000000^3571 ≤ 33282061581647^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063227309 2500000000 33282061581647 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11248623/25000000 : ℝ)^4595 ≤ (35785020271071/100000000000000 : ℝ)^3571 := by
    have hnat : (11248623 : ℕ)^4595*100000000000000^3571 ≤ 35785020271071^3571*25000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11248623 25000000 35785020271071 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008866479/5000000000 : ℝ)^4595 ≤ (30932918128463/100000000000000 : ℝ)^3571 := by
    have hnat : (2008866479 : ℕ)^4595*100000000000000^3571 ≤ 30932918128463^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008866479 5000000000 30932918128463 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063227309/2500000000 : ℝ), (11248623/25000000 : ℝ), (2008866479/5000000000 : ℝ)] ![(33282061581647/100000000000000 : ℝ), (35785020271071/100000000000000 : ℝ), (30932918128463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063227309/2500000000 : ℝ)|^4595 ≤ (33282061581647/100000000000000 : ℝ)^3571
        have hw : |(1063227309/2500000000 : ℝ)|=(1063227309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11248623/25000000 : ℝ)|^4595 ≤ (35785020271071/100000000000000 : ℝ)^3571
        have hw : |(11248623/25000000 : ℝ)|=(11248623/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008866479/5000000000 : ℝ)|^4595 ≤ (30932918128463/100000000000000 : ℝ)^3571
        have hw : |(2008866479/5000000000 : ℝ)|=(2008866479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1549_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11047/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11047/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11047/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11047/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11047/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11047/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11047/100000 : ℝ) ^ (4593/1024 : ℝ) ≤ (204491169947311/4000000000000000000 : ℝ) := by
    have hpowers : (11047/100000 : ℝ)^4593 ≤ (204491169947311/4000000000000000000 : ℝ)^1024 := by
      have hnat : (11047 : ℕ)^4593*4000000000000000000^1024 ≤ 204491169947311^1024*100000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11047 100000 204491169947311 4000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11047/100000 : ℝ)) (X := (204491169947311/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4593/1024 : ℝ) ≤ (1164302595054771/5000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4593 ≤ (1164302595054771/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4593*5000000000000000000^1024 ≤ 1164302595054771^1024*10000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 1164302595054771 5000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (1164302595054771/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000204491169947311/2000000000000000000 : ℝ) ≤ (10000227945395321/10000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (2000204491169947311/2000000000000000000 : ℝ)^1024 ≤ (10000227945395321/10000000000000000 : ℝ)^4593 := by
      have hnat : (2000204491169947311 : ℕ)^1024*10000000000000000^4593 ≤ 10000227945395321^4593*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000204491169947311 2000000000000000000 10000227945395321 10000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000227945395321/10000000000000000 : ℝ)) (X := (2000204491169947311/2000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005679666229955639/20000000000000000000 : ℝ) ≤ (400025322606671/400000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (20005679666229955639/20000000000000000000 : ℝ)^1024 ≤ (400025322606671/400000000000000 : ℝ)^4593 := by
      have hnat : (20005679666229955639 : ℕ)^1024*400000000000000^4593 ≤ 400025322606671^4593*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005679666229955639 20000000000000000000 400025322606671 400000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025322606671/400000000000000 : ℝ)) (X := (20005679666229955639/20000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501164302595054771/2500000000000000000 : ℝ) ≤ (10001038184938229/10000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (2501164302595054771/2500000000000000000 : ℝ)^1024 ≤ (10001038184938229/10000000000000000 : ℝ)^4593 := by
      have hnat : (2501164302595054771 : ℕ)^1024*10000000000000000^4593 ≤ 10001038184938229^4593*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501164302595054771 2500000000000000000 10001038184938229 10000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001038184938229/10000000000000000 : ℝ)) (X := (2501164302595054771/2500000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(204491169947311/4000000000000000000 : ℝ) ≤ ((14807354015053635509/14810000000000000000 : ℝ)+2*(67519961909/74050000000000 : ℝ)*(11047/100000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (14807354015053635509/14810000000000000000 : ℝ)+2*(67519961909/74050000000000 : ℝ)*(11047/100000 : ℝ)=(10000227945395321/10000000000000000 : ℝ) by norm_num, show 1+2*(204491169947311/4000000000000000000 : ℝ)=(2000204491169947311/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1164302595054771/5000000000000000000 : ℝ)+(204491169947311/4000000000000000000 : ℝ) ≤ ((14807354015053635509/14810000000000000000 : ℝ)+(67519961909/74050000000000 : ℝ)*((1549/10000 : ℝ)+(11047/100000 : ℝ)))^(4593/1024 : ℝ) := by
    rw [show (14807354015053635509/14810000000000000000 : ℝ)+(67519961909/74050000000000 : ℝ)*((1549/10000 : ℝ)+(11047/100000 : ℝ))=(400025322606671/400000000000000 : ℝ) by norm_num, show 1+(1164302595054771/5000000000000000000 : ℝ)+(204491169947311/4000000000000000000 : ℝ)=(20005679666229955639/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1164302595054771/5000000000000000000 : ℝ) ≤ ((14807354015053635509/14810000000000000000 : ℝ)+2*(67519961909/74050000000000 : ℝ)*(1549/10000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (14807354015053635509/14810000000000000000 : ℝ)+2*(67519961909/74050000000000 : ℝ)*(1549/10000 : ℝ)=(10001038184938229/10000000000000000 : ℝ) by norm_num, show 1+2*(1164302595054771/5000000000000000000 : ℝ)=(2501164302595054771/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14807354015053635509/14810000000000000000 : ℝ)*(X 1 0+X 2 0)+(67519961909/74050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (11047/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (14807354015053635509/14810000000000000000 : ℝ)) (alpha := (67519961909/74050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14807354015053635509/14810000000000000000 : ℝ)*(X 0 1+X 2 1)+(67519961909/74050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (11047/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (14807354015053635509/14810000000000000000 : ℝ)) (alpha := (67519961909/74050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14807354015053635509/14810000000000000000 : ℝ)*(X 0 2+X 1 2)+(67519961909/74050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (11047/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (14807354015053635509/14810000000000000000 : ℝ)) (alpha := (67519961909/74050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-907352861/5000000000 : ℝ)*X 0 0+(5428482441/10000000000 : ℝ)*X 0 1+(5219277363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42795727/80000000 : ℝ)*X 1 0+(-1921773391/10000000000 : ℝ)*X 1 1+(5219277231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349465919/10000000000 : ℝ)*X 2 0+(2609638579/5000000000 : ℝ)*X 2 1+(-192177343/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((85056903/200000000 : ℝ)*X 0 0+(2007594869/5000000000 : ℝ)*X 0 1+(2250986899/5000000000 : ℝ)*X 0 2+(85056903/200000000 : ℝ)*X 1 0+(2007594869/5000000000 : ℝ)*X 1 1+(2250986899/5000000000 : ℝ)*X 1 2+(85056903/200000000 : ℝ)*X 2 0+(2007594869/5000000000 : ℝ)*X 2 1+(2250986899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1814733307/10000000000 : ℝ)*X 0 0+(2610181283/5000000000 : ℝ)*X 0 1+(5427389189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323565123/2500000000 : ℝ)*X 1 0+(-214207717/1250000000 : ℝ)*X 1 1+(542738947/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058852169/2000000000 : ℝ)*X 2 0+(5427389329/10000000000 : ℝ)*X 2 1+(-428415361/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1063227309/2500000000 : ℝ)*X 0 0+(11248623/25000000 : ℝ)*X 0 1+(2008866479/5000000000 : ℝ)*X 0 2+(1063227309/2500000000 : ℝ)*X 1 0+(11248623/25000000 : ℝ)*X 1 1+(2008866479/5000000000 : ℝ)*X 1 2+(1063227309/2500000000 : ℝ)*X 2 0+(11248623/25000000 : ℝ)*X 2 1+(2008866479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133256423900368823700553101/46281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83621501/6250000000000 : ℝ)*(base19) + (1172927649/100000000000000 : ℝ)*(base23) + (107857889/50000000000000 : ℝ)*(upper3) + (13663387/12500000000000 : ℝ)*(upper4) + (41527067/100000000000000 : ℝ)*(upper5) + (427146813506487/12500000000000 : ℝ)*(major0) + (427146813506487/12500000000000 : ℝ)*(major1) + (427146813506487/12500000000000 : ℝ)*(major2) + (597502342563129/12500000000000 : ℝ)*(sp0) + (4780034740436289/100000000000000 : ℝ)*(sp1) + (298752181590791/6250000000000 : ℝ)*(sp2) + (82172183924723/4000000000000 : ℝ)*(sp3) + (17337875273/100000000000000 : ℝ)*(sp4) + (8243629591/100000000000000 : ℝ)*(sp7) + (1027156420873833/50000000000000 : ℝ)*(f.failure) + (956007215676061/20000000000000 : ℝ)*(f.sum) + (2277870268473/7405000000000000000000000000 : ℝ)*base65 + (412649530294146883/185125000000000000000000000000000 : ℝ)*base67 + (354926063001521883/185125000000000000000000000000000 : ℝ)*base69 + (1735726534731521883/185125000000000000000000000000000 : ℝ)*base71 + (608063646227/7405000000000000000000000000 : ℝ)*base74 + (990271074298271883/185125000000000000000000000000000 : ℝ)*base75 + (1750000970142896883/185125000000000000000000000000000 : ℝ)*base77 + (750094310288103117/185125000000000000000000000000000 : ℝ)*base80 + (6443717475253/1851250000000000000000000000 : ℝ)*base82 + (132081/2500000000000000000000 : ℝ)*base90 + (132081/2500000000000000000000 : ℝ)*base92 + (132081/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1623322470928974235610319189/370250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11613657/2000000000000 : ℝ)*(base19) + (318514157/25000000000000 : ℝ)*(base23) + (184238169/100000000000000 : ℝ)*(lower1) + (122214999/100000000000000 : ℝ)*(upper2) + (108508249/50000000000000 : ℝ)*(upper3) + (1665331/1250000000000 : ℝ)*(upper5) + (1726548436019493/50000000000000 : ℝ)*(major0) + (1726548436019493/50000000000000 : ℝ)*(major1) + (1726548436019493/50000000000000 : ℝ)*(major2) + (13470884677/100000000000000 : ℝ)*(sp2) + (4830285203053343/100000000000000 : ℝ)*(sp4) + (4830284622370493/100000000000000 : ℝ)*(sp5) + (2415135229056019/50000000000000 : ℝ)*(sp6) + (259488549359763/12500000000000 : ℝ)*(sp7) + (259488549359763/12500000000000 : ℝ)*(f.failure) + (4830285203053343/100000000000000 : ℝ)*(f.sum) + (34780215895867/7405000000000000000000000000 : ℝ)*base66 + (8324289461279376937/740500000000000000000000000000000 : ℝ)*base67 + (7904645917021123063/740500000000000000000000000000000 : ℝ)*base70 + (2118265473318376937/740500000000000000000000000000000 : ℝ)*base71 + (6642945279747/1851250000000000000000000000 : ℝ)*base73 + (2048858969617376937/740500000000000000000000000000000 : ℝ)*base75 + (340870393620123063/740500000000000000000000000000000 : ℝ)*base78 + (1994797340914376937/740500000000000000000000000000000 : ℝ)*base79 + (37649386012351/3702500000000000000000000000 : ℝ)*base82 + (513909/625000000000000000000 : ℝ)*base89 + (513909/625000000000000000000 : ℝ)*base91 + (513909/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1549_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1549_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1549_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1549_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1549_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1549_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1549_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
