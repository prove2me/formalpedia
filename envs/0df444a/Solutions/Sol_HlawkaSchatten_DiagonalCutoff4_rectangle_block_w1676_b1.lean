-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1676_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:53.096526+00:00
-- url     : https://prove2.me/submissions/fd9c2c4d-b364-4450-aeb4-fa13f6d406d6

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
theorem support_rectangle_w1676_s3_0 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-154508311/1000000000 : ℝ)*x 0 + (2746469383/5000000000 : ℝ)*x 1 + (1283122513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (154508311/1000000000 : ℝ)^5031 ≤ (1917415474009/20000000000000 : ℝ)^4007 := by
    have hnat : (154508311 : ℕ)^5031*20000000000000^4007 ≤ 1917415474009^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154508311 1000000000 1917415474009 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746469383/5000000000 : ℝ)^5031 ≤ (23565743361081/50000000000000 : ℝ)^4007 := by
    have hnat : (2746469383 : ℕ)^5031*50000000000000^4007 ≤ 23565743361081^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746469383 5000000000 23565743361081 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283122513/2500000000 : ℝ)^5031 ≤ (2705089743121/6250000000000 : ℝ)^4007 := by
    have hnat : (1283122513 : ℕ)^5031*6250000000000^4007 ≤ 2705089743121^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283122513 2500000000 2705089743121 6250000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-154508311/1000000000 : ℝ), (2746469383/5000000000 : ℝ), (1283122513/2500000000 : ℝ)] ![(1917415474009/20000000000000 : ℝ), (23565743361081/50000000000000 : ℝ), (2705089743121/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-154508311/1000000000 : ℝ)|^5031 ≤ (1917415474009/20000000000000 : ℝ)^4007
        have hw : |(-154508311/1000000000 : ℝ)|=(154508311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746469383/5000000000 : ℝ)|^5031 ≤ (23565743361081/50000000000000 : ℝ)^4007
        have hw : |(2746469383/5000000000 : ℝ)|=(2746469383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283122513/2500000000 : ℝ)|^5031 ≤ (2705089743121/6250000000000 : ℝ)^4007
        have hw : |(1283122513/2500000000 : ℝ)|=(1283122513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s3_1 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677434149/5000000000 : ℝ)*x 0 + (-866285763/5000000000 : ℝ)*x 1 + (2566245047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677434149/5000000000 : ℝ)^5031 ≤ (22824422491573/50000000000000 : ℝ)^4007 := by
    have hnat : (2677434149 : ℕ)^5031*50000000000000^4007 ≤ 22824422491573^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677434149 5000000000 22824422491573 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866285763/5000000000 : ℝ)^5031 ≤ (11069718663411/100000000000000 : ℝ)^4007 := by
    have hnat : (866285763 : ℕ)^5031*100000000000000^4007 ≤ 11069718663411^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866285763 5000000000 11069718663411 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566245047/5000000000 : ℝ)^5031 ≤ (21640718167313/50000000000000 : ℝ)^4007 := by
    have hnat : (2566245047 : ℕ)^5031*50000000000000^4007 ≤ 21640718167313^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566245047 5000000000 21640718167313 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677434149/5000000000 : ℝ), (-866285763/5000000000 : ℝ), (2566245047/5000000000 : ℝ)] ![(22824422491573/50000000000000 : ℝ), (11069718663411/100000000000000 : ℝ), (21640718167313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677434149/5000000000 : ℝ)|^5031 ≤ (22824422491573/50000000000000 : ℝ)^4007
        have hw : |(2677434149/5000000000 : ℝ)|=(2677434149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-866285763/5000000000 : ℝ)|^5031 ≤ (11069718663411/100000000000000 : ℝ)^4007
        have hw : |(-866285763/5000000000 : ℝ)|=(866285763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566245047/5000000000 : ℝ)|^5031 ≤ (21640718167313/50000000000000 : ℝ)^4007
        have hw : |(2566245047/5000000000 : ℝ)|=(2566245047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s3_2 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338717121/2500000000 : ℝ)*x 0 + (1283122523/2500000000 : ℝ)*x 1 + (-1732571281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338717121/2500000000 : ℝ)^5031 ≤ (44578952123/97656250000 : ℝ)^4007 := by
    have hnat : (1338717121 : ℕ)^5031*97656250000^4007 ≤ 44578952123^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338717121 2500000000 44578952123 97656250000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283122523/2500000000 : ℝ)^5031 ≤ (43281436313451/100000000000000 : ℝ)^4007 := by
    have hnat : (1283122523 : ℕ)^5031*100000000000000^4007 ≤ 43281436313451^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283122523 2500000000 43281436313451 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732571281/10000000000 : ℝ)^5031 ≤ (691857293627/6250000000000 : ℝ)^4007 := by
    have hnat : (1732571281 : ℕ)^5031*6250000000000^4007 ≤ 691857293627^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732571281 10000000000 691857293627 6250000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338717121/2500000000 : ℝ), (1283122523/2500000000 : ℝ), (-1732571281/10000000000 : ℝ)] ![(44578952123/97656250000 : ℝ), (43281436313451/100000000000000 : ℝ), (691857293627/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338717121/2500000000 : ℝ)|^5031 ≤ (44578952123/97656250000 : ℝ)^4007
        have hw : |(1338717121/2500000000 : ℝ)|=(1338717121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283122523/2500000000 : ℝ)|^5031 ≤ (43281436313451/100000000000000 : ℝ)^4007
        have hw : |(1283122523/2500000000 : ℝ)|=(1283122523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1732571281/10000000000 : ℝ)|^5031 ≤ (691857293627/6250000000000 : ℝ)^4007
        have hw : |(-1732571281/10000000000 : ℝ)|=(1732571281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s3_3 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2075446079/5000000000 : ℝ)*x 0 + (3688145489/10000000000 : ℝ)*x 1 + (4652507777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075446079/5000000000 : ℝ)^5031 ≤ (33155565180319/100000000000000 : ℝ)^4007 := by
    have hnat : (2075446079 : ℕ)^5031*100000000000000^4007 ≤ 33155565180319^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075446079 5000000000 33155565180319 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688145489/10000000000 : ℝ)^5031 ≤ (7145697771981/25000000000000 : ℝ)^4007 := by
    have hnat : (3688145489 : ℕ)^5031*25000000000000^4007 ≤ 7145697771981^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688145489 10000000000 7145697771981 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4652507777/10000000000 : ℝ)^5031 ≤ (765232874507/2000000000000 : ℝ)^4007 := by
    have hnat : (4652507777 : ℕ)^5031*2000000000000^4007 ≤ 765232874507^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4652507777 10000000000 765232874507 2000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2075446079/5000000000 : ℝ), (3688145489/10000000000 : ℝ), (4652507777/10000000000 : ℝ)] ![(33155565180319/100000000000000 : ℝ), (7145697771981/25000000000000 : ℝ), (765232874507/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2075446079/5000000000 : ℝ)|^5031 ≤ (33155565180319/100000000000000 : ℝ)^4007
        have hw : |(2075446079/5000000000 : ℝ)|=(2075446079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688145489/10000000000 : ℝ)|^5031 ≤ (7145697771981/25000000000000 : ℝ)^4007
        have hw : |(3688145489/10000000000 : ℝ)|=(3688145489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4652507777/10000000000 : ℝ)|^5031 ≤ (765232874507/2000000000000 : ℝ)^4007
        have hw : |(4652507777/10000000000 : ℝ)|=(4652507777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s3_4 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-193156863/1250000000 : ℝ)*x 0 + (2568182757/5000000000 : ℝ)*x 1 + (5489004983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193156863/1250000000 : ℝ)^5031 ≤ (2397103940659/25000000000000 : ℝ)^4007 := by
    have hnat : (193156863 : ℕ)^5031*25000000000000^4007 ≤ 2397103940659^4007*1250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193156863 1250000000 2397103940659 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568182757/5000000000 : ℝ)^5031 ≤ (21661236364143/50000000000000 : ℝ)^4007 := by
    have hnat : (2568182757 : ℕ)^5031*50000000000000^4007 ≤ 21661236364143^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568182757 5000000000 21661236364143 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489004983/10000000000 : ℝ)^5031 ≤ (1471534734321/3125000000000 : ℝ)^4007 := by
    have hnat : (5489004983 : ℕ)^5031*3125000000000^4007 ≤ 1471534734321^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489004983 10000000000 1471534734321 3125000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-193156863/1250000000 : ℝ), (2568182757/5000000000 : ℝ), (5489004983/10000000000 : ℝ)] ![(2397103940659/25000000000000 : ℝ), (21661236364143/50000000000000 : ℝ), (1471534734321/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-193156863/1250000000 : ℝ)|^5031 ≤ (2397103940659/25000000000000 : ℝ)^4007
        have hw : |(-193156863/1250000000 : ℝ)|=(193156863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568182757/5000000000 : ℝ)|^5031 ≤ (21661236364143/50000000000000 : ℝ)^4007
        have hw : |(2568182757/5000000000 : ℝ)|=(2568182757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489004983/10000000000 : ℝ)|^5031 ≤ (1471534734321/3125000000000 : ℝ)^4007
        have hw : |(5489004983/10000000000 : ℝ)|=(5489004983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s3_5 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314670079/2500000000 : ℝ)*x 0 + (-1376056931/10000000000 : ℝ)*x 1 + (5489004629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314670079/2500000000 : ℝ)^5031 ≤ (22310846917449/50000000000000 : ℝ)^4007 := by
    have hnat : (1314670079 : ℕ)^5031*50000000000000^4007 ≤ 22310846917449^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314670079 2500000000 22310846917449 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376056931/10000000000 : ℝ)^5031 ≤ (4144599232087/50000000000000 : ℝ)^4007 := by
    have hnat : (1376056931 : ℕ)^5031*50000000000000^4007 ≤ 4144599232087^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376056931 10000000000 4144599232087 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489004629/10000000000 : ℝ)^5031 ≤ (47089107685287/100000000000000 : ℝ)^4007 := by
    have hnat : (5489004629 : ℕ)^5031*100000000000000^4007 ≤ 47089107685287^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489004629 10000000000 47089107685287 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314670079/2500000000 : ℝ), (-1376056931/10000000000 : ℝ), (5489004629/10000000000 : ℝ)] ![(22310846917449/50000000000000 : ℝ), (4144599232087/50000000000000 : ℝ), (47089107685287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314670079/2500000000 : ℝ)|^5031 ≤ (22310846917449/50000000000000 : ℝ)^4007
        have hw : |(1314670079/2500000000 : ℝ)|=(1314670079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1376056931/10000000000 : ℝ)|^5031 ≤ (4144599232087/50000000000000 : ℝ)^4007
        have hw : |(-1376056931/10000000000 : ℝ)|=(1376056931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489004629/10000000000 : ℝ)|^5031 ≤ (47089107685287/100000000000000 : ℝ)^4007
        have hw : |(5489004629/10000000000 : ℝ)|=(5489004629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s3_6 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258680321/10000000000 : ℝ)*x 0 + (1097801019/2000000000 : ℝ)*x 1 + (-688028131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258680321/10000000000 : ℝ)^5031 ≤ (44621693888167/100000000000000 : ℝ)^4007 := by
    have hnat : (5258680321 : ℕ)^5031*100000000000000^4007 ≤ 44621693888167^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258680321 10000000000 44621693888167 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097801019/2000000000 : ℝ)^5031 ≤ (73576738601/156250000000 : ℝ)^4007 := by
    have hnat : (1097801019 : ℕ)^5031*156250000000^4007 ≤ 73576738601^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097801019 2000000000 73576738601 156250000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688028131/5000000000 : ℝ)^5031 ≤ (8289193404329/100000000000000 : ℝ)^4007 := by
    have hnat : (688028131 : ℕ)^5031*100000000000000^4007 ≤ 8289193404329^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688028131 5000000000 8289193404329 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258680321/10000000000 : ℝ), (1097801019/2000000000 : ℝ), (-688028131/5000000000 : ℝ)] ![(44621693888167/100000000000000 : ℝ), (73576738601/156250000000 : ℝ), (8289193404329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258680321/10000000000 : ℝ)|^5031 ≤ (44621693888167/100000000000000 : ℝ)^4007
        have hw : |(5258680321/10000000000 : ℝ)|=(5258680321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097801019/2000000000 : ℝ)|^5031 ≤ (73576738601/156250000000 : ℝ)^4007
        have hw : |(1097801019/2000000000 : ℝ)|=(1097801019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-688028131/5000000000 : ℝ)|^5031 ≤ (8289193404329/100000000000000 : ℝ)^4007
        have hw : |(-688028131/5000000000 : ℝ)|=(688028131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s3_7 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4151349993/10000000000 : ℝ)*x 0 + (4642138237/10000000000 : ℝ)*x 1 + (3698670353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151349993/10000000000 : ℝ)^5031 ≤ (16580078395569/50000000000000 : ℝ)^4007 := by
    have hnat : (4151349993 : ℕ)^5031*50000000000000^4007 ≤ 16580078395569^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151349993 10000000000 16580078395569 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4642138237/10000000000 : ℝ)^5031 ≤ (2384662715689/6250000000000 : ℝ)^4007 := by
    have hnat : (4642138237 : ℕ)^5031*6250000000000^4007 ≤ 2384662715689^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4642138237 10000000000 2384662715689 6250000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3698670353/10000000000 : ℝ)^5031 ≤ (14342619873261/50000000000000 : ℝ)^4007 := by
    have hnat : (3698670353 : ℕ)^5031*50000000000000^4007 ≤ 14342619873261^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698670353 10000000000 14342619873261 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151349993/10000000000 : ℝ), (4642138237/10000000000 : ℝ), (3698670353/10000000000 : ℝ)] ![(16580078395569/50000000000000 : ℝ), (2384662715689/6250000000000 : ℝ), (14342619873261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151349993/10000000000 : ℝ)|^5031 ≤ (16580078395569/50000000000000 : ℝ)^4007
        have hw : |(4151349993/10000000000 : ℝ)|=(4151349993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4642138237/10000000000 : ℝ)|^5031 ≤ (2384662715689/6250000000000 : ℝ)^4007
        have hw : |(4642138237/10000000000 : ℝ)|=(4642138237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3698670353/10000000000 : ℝ)|^5031 ≤ (14342619873261/50000000000000 : ℝ)^4007
        have hw : |(3698670353/10000000000 : ℝ)|=(3698670353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1676_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9679/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3467/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17371/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (603/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17371/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (603/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17371/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (603/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17371/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (603/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17371/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (603/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17371/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (603/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (603/6250 : ℝ) ^ (5023/1024 : ℝ) ≤ (208649444937509/20000000000000000000 : ℝ) := by
    have hpowers : (603/6250 : ℝ)^5023 ≤ (208649444937509/20000000000000000000 : ℝ)^1024 := by
      have hnat : (603 : ℕ)^5023*20000000000000000000^1024 ≤ 208649444937509^1024*6250^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        603 6250 208649444937509 20000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (603/6250 : ℝ)) (X := (208649444937509/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17371/100000 : ℝ) ^ (5023/1024 : ℝ) ≤ (46673771078247/250000000000000000 : ℝ) := by
    have hpowers : (17371/100000 : ℝ)^5023 ≤ (46673771078247/250000000000000000 : ℝ)^1024 := by
      have hnat : (17371 : ℕ)^5023*250000000000000000^1024 ≤ 46673771078247^1024*100000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17371 100000 46673771078247 250000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17371/100000 : ℝ)) (X := (46673771078247/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000208649444937509/10000000000000000000 : ℝ) ≤ (10000042535388627/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (10000208649444937509/10000000000000000000 : ℝ)^1024 ≤ (10000042535388627/10000000000000000 : ℝ)^5023 := by
      have hnat : (10000208649444937509 : ℕ)^1024*10000000000000000^5023 ≤ 10000042535388627^5023*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000208649444937509 10000000000000000000 10000042535388627 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042535388627/10000000000000000 : ℝ)) (X := (10000208649444937509/10000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003942551131197269/20000000000000000000 : ℝ) ≤ (10000401837109041/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (20003942551131197269/20000000000000000000 : ℝ)^1024 ≤ (10000401837109041/10000000000000000 : ℝ)^5023 := by
      have hnat : (20003942551131197269 : ℕ)^1024*10000000000000000^5023 ≤ 10000401837109041^5023*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003942551131197269 20000000000000000000 10000401837109041 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000401837109041/10000000000000000 : ℝ)) (X := (20003942551131197269/20000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (125046673771078247/125000000000000000 : ℝ) ≤ (2000152227765891/2000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (125046673771078247/125000000000000000 : ℝ)^1024 ≤ (2000152227765891/2000000000000000 : ℝ)^5023 := by
      have hnat : (125046673771078247 : ℕ)^1024*2000000000000000^5023 ≤ 2000152227765891^5023*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125046673771078247 125000000000000000 2000152227765891 2000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000152227765891/2000000000000000 : ℝ)) (X := (125046673771078247/125000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(208649444937509/20000000000000000000 : ℝ) ≤ ((77223395414809257777/77230000000000000000 : ℝ)+2*(179650860207/386150000000000 : ℝ)*(603/6250 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (77223395414809257777/77230000000000000000 : ℝ)+2*(179650860207/386150000000000 : ℝ)*(603/6250 : ℝ)=(10000042535388627/10000000000000000 : ℝ) by norm_num, show 1+2*(208649444937509/20000000000000000000 : ℝ)=(10000208649444937509/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46673771078247/250000000000000000 : ℝ)+(208649444937509/20000000000000000000 : ℝ) ≤ ((77223395414809257777/77230000000000000000 : ℝ)+(179650860207/386150000000000 : ℝ)*((17371/100000 : ℝ)+(603/6250 : ℝ)))^(5023/1024 : ℝ) := by
    rw [show (77223395414809257777/77230000000000000000 : ℝ)+(179650860207/386150000000000 : ℝ)*((17371/100000 : ℝ)+(603/6250 : ℝ))=(10000401837109041/10000000000000000 : ℝ) by norm_num, show 1+(46673771078247/250000000000000000 : ℝ)+(208649444937509/20000000000000000000 : ℝ)=(20003942551131197269/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46673771078247/250000000000000000 : ℝ) ≤ ((77223395414809257777/77230000000000000000 : ℝ)+2*(179650860207/386150000000000 : ℝ)*(17371/100000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (77223395414809257777/77230000000000000000 : ℝ)+2*(179650860207/386150000000000 : ℝ)*(17371/100000 : ℝ)=(2000152227765891/2000000000000000 : ℝ) by norm_num, show 1+2*(46673771078247/250000000000000000 : ℝ)=(125046673771078247/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (77223395414809257777/77230000000000000000 : ℝ)*(X 1 0+X 2 0)+(179650860207/386150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (603/6250 : ℝ)) (hi := (17371/100000 : ℝ)) (c := (77223395414809257777/77230000000000000000 : ℝ)) (alpha := (179650860207/386150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (77223395414809257777/77230000000000000000 : ℝ)*(X 0 1+X 2 1)+(179650860207/386150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (603/6250 : ℝ)) (hi := (17371/100000 : ℝ)) (c := (77223395414809257777/77230000000000000000 : ℝ)) (alpha := (179650860207/386150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (77223395414809257777/77230000000000000000 : ℝ)*(X 0 2+X 1 2)+(179650860207/386150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (603/6250 : ℝ)) (hi := (17371/100000 : ℝ)) (c := (77223395414809257777/77230000000000000000 : ℝ)) (alpha := (179650860207/386150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-154508311/1000000000 : ℝ)*X 0 0+(2746469383/5000000000 : ℝ)*X 0 1+(1283122513/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677434149/5000000000 : ℝ)*X 1 0+(-866285763/5000000000 : ℝ)*X 1 1+(2566245047/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338717121/2500000000 : ℝ)*X 2 0+(1283122523/2500000000 : ℝ)*X 2 1+(-1732571281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2075446079/5000000000 : ℝ)*X 0 0+(3688145489/10000000000 : ℝ)*X 0 1+(4652507777/10000000000 : ℝ)*X 0 2+(2075446079/5000000000 : ℝ)*X 1 0+(3688145489/10000000000 : ℝ)*X 1 1+(4652507777/10000000000 : ℝ)*X 1 2+(2075446079/5000000000 : ℝ)*X 2 0+(3688145489/10000000000 : ℝ)*X 2 1+(4652507777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-193156863/1250000000 : ℝ)*X 0 0+(2568182757/5000000000 : ℝ)*X 0 1+(5489004983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314670079/2500000000 : ℝ)*X 1 0+(-1376056931/10000000000 : ℝ)*X 1 1+(5489004629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258680321/10000000000 : ℝ)*X 2 0+(1097801019/2000000000 : ℝ)*X 2 1+(-688028131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4151349993/10000000000 : ℝ)*X 0 0+(4642138237/10000000000 : ℝ)*X 0 1+(3698670353/10000000000 : ℝ)*X 0 2+(4151349993/10000000000 : ℝ)*X 1 0+(4642138237/10000000000 : ℝ)*X 1 1+(3698670353/10000000000 : ℝ)*X 1 2+(4151349993/10000000000 : ℝ)*X 2 0+(4642138237/10000000000 : ℝ)*X 2 1+(3698670353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7266610609745150990724792813/965375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248239263/25000000000000 : ℝ)*(base19) + (100385681/10000000000000 : ℝ)*(base23) + (2860377/6250000000000 : ℝ)*(lower2) + (82239977/100000000000000 : ℝ)*(upper3) + (88939687/50000000000000 : ℝ)*(upper5) + (476412824053259/25000000000000 : ℝ)*(major0) + (476412824053259/25000000000000 : ℝ)*(major1) + (476412824053259/25000000000000 : ℝ)*(major2) + (277432859310149/10000000000000 : ℝ)*(sp0) + (2774339177081191/100000000000000 : ℝ)*(sp1) + (2774339166181433/100000000000000 : ℝ)*(sp2) + (259239631564849/25000000000000 : ℝ)*(sp3) + (11576936753/100000000000000 : ℝ)*(sp4) + (911305093/25000000000000 : ℝ)*(sp7) + (129620271434971/12500000000000 : ℝ)*(f.failure) + (693585042509561/25000000000000 : ℝ)*(f.sum) + (12023731589339/2413437500000000000000000000 : ℝ)*base65 + (18795863845088045243/1930750000000000000000000000000000 : ℝ)*base67 + (15313282226755295243/1930750000000000000000000000000000 : ℝ)*base69 + (13136004036509045243/1930750000000000000000000000000000 : ℝ)*base71 + (36199365197787/19307500000000000000000000000 : ℝ)*base73 + (22462841222799045243/1930750000000000000000000000000000 : ℝ)*base75 + (20203177198298545243/1930750000000000000000000000000000 : ℝ)*base77 + (26740582575527545243/1930750000000000000000000000000000 : ℝ)*base79 + (89362091539121/38615000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13337471/1250000000000000000000 : ℝ)*base90 + (13337471/1250000000000000000000 : ℝ)*base92 + (13337471/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19962112848396450547345027059/1930750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1559964961/100000000000000 : ℝ)*(base19) + (1910251283/100000000000000 : ℝ)*(base23) + (41830301/10000000000000 : ℝ)*(lower1) + (25883277/20000000000000 : ℝ)*(upper2) + (185011031/100000000000000 : ℝ)*(upper3) + (318094953/100000000000000 : ℝ)*(upper5) + (1947830578142689/100000000000000 : ℝ)*(major0) + (1947830578142689/100000000000000 : ℝ)*(major1) + (1947830578142689/100000000000000 : ℝ)*(major2) + (5548512403/100000000000000 : ℝ)*(sp2) + (567149347845689/20000000000000 : ℝ)*(sp4) + (708936294815871/25000000000000 : ℝ)*(sp5) + (2835739280464759/100000000000000 : ℝ)*(sp6) + (52995703621103/5000000000000 : ℝ)*(sp7) + (52995703621103/5000000000000 : ℝ)*(f.failure) + (567149347845689/20000000000000 : ℝ)*(f.sum) + (14955801726873/19307500000000000000000000000 : ℝ)*base65 + (24769741917236457647/7723000000000000000000000000000000 : ℝ)*base68 + (318928576355031457647/7723000000000000000000000000000000 : ℝ)*base70 + (67631407806238457647/7723000000000000000000000000000000 : ℝ)*base72 + (1135055566797/19307500000000000000000000000 : ℝ)*base74 + (27820332060754457647/7723000000000000000000000000000000 : ℝ)*base76 + (91624712534319457647/7723000000000000000000000000000000 : ℝ)*base78 + (21647708823690542353/7723000000000000000000000000000000 : ℝ)*base79 + (903077643967339/38615000000000000000000000000 : ℝ)*base82 + (2446397/500000000000000000000 : ℝ)*base89 + (2446397/500000000000000000000 : ℝ)*base91 + (2446397/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1676_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9679/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3467/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1676_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1676_s4_0 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61804361/400000000 : ℝ)*x 0 + (1373210121/2500000000 : ℝ)*x 1 + (641571373/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61804361/400000000 : ℝ)^5031 ≤ (9587279263159/100000000000000 : ℝ)^4007 := by
    have hnat : (61804361 : ℕ)^5031*100000000000000^4007 ≤ 9587279263159^4007*400000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61804361 400000000 9587279263159 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373210121/2500000000 : ℝ)^5031 ≤ (9426085584229/20000000000000 : ℝ)^4007 := by
    have hnat : (1373210121 : ℕ)^5031*20000000000000^4007 ≤ 9426085584229^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373210121 2500000000 9426085584229 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641571373/1250000000 : ℝ)^5031 ≤ (43282292788997/100000000000000 : ℝ)^4007 := by
    have hnat : (641571373 : ℕ)^5031*100000000000000^4007 ≤ 43282292788997^4007*1250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641571373 1250000000 43282292788997 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61804361/400000000 : ℝ), (1373210121/2500000000 : ℝ), (641571373/1250000000 : ℝ)] ![(9587279263159/100000000000000 : ℝ), (9426085584229/20000000000000 : ℝ), (43282292788997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61804361/400000000 : ℝ)|^5031 ≤ (9587279263159/100000000000000 : ℝ)^4007
        have hw : |(-61804361/400000000 : ℝ)|=(61804361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373210121/2500000000 : ℝ)|^5031 ≤ (9426085584229/20000000000000 : ℝ)^4007
        have hw : |(1373210121/2500000000 : ℝ)|=(1373210121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641571373/1250000000 : ℝ)|^5031 ≤ (43282292788997/100000000000000 : ℝ)^4007
        have hw : |(641571373/1250000000 : ℝ)|=(641571373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s4_1 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338710343/2500000000 : ℝ)*x 0 + (-866250387/5000000000 : ℝ)*x 1 + (128314273/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338710343/2500000000 : ℝ)^5031 ≤ (2282427839371/5000000000000 : ℝ)^4007 := by
    have hnat : (1338710343 : ℕ)^5031*5000000000000^4007 ≤ 2282427839371^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338710343 2500000000 2282427839371 5000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866250387/5000000000 : ℝ)^5031 ≤ (5534575548399/50000000000000 : ℝ)^4007 := by
    have hnat : (866250387 : ℕ)^5031*50000000000000^4007 ≤ 5534575548399^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866250387 5000000000 5534575548399 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128314273/250000000 : ℝ)^5031 ≤ (4328229211137/10000000000000 : ℝ)^4007 := by
    have hnat : (128314273 : ℕ)^5031*10000000000000^4007 ≤ 4328229211137^4007*250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128314273 250000000 4328229211137 10000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338710343/2500000000 : ℝ), (-866250387/5000000000 : ℝ), (128314273/250000000 : ℝ)] ![(2282427839371/5000000000000 : ℝ), (5534575548399/50000000000000 : ℝ), (4328229211137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338710343/2500000000 : ℝ)|^5031 ≤ (2282427839371/5000000000000 : ℝ)^4007
        have hw : |(1338710343/2500000000 : ℝ)|=(1338710343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-866250387/5000000000 : ℝ)|^5031 ≤ (5534575548399/50000000000000 : ℝ)^4007
        have hw : |(-866250387/5000000000 : ℝ)|=(866250387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128314273/250000000 : ℝ)|^5031 ≤ (4328229211137/10000000000000 : ℝ)^4007
        have hw : |(128314273/250000000 : ℝ)|=(128314273/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s4_2 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354841819/10000000000 : ℝ)*x 0 + (5132570657/10000000000 : ℝ)*x 1 + (-1732500523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354841819/10000000000 : ℝ)^5031 ≤ (4564856157177/10000000000000 : ℝ)^4007 := by
    have hnat : (5354841819 : ℕ)^5031*10000000000000^4007 ≤ 4564856157177^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354841819 10000000000 4564856157177 10000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132570657/10000000000 : ℝ)^5031 ≤ (173129157307/400000000000 : ℝ)^4007 := by
    have hnat : (5132570657 : ℕ)^5031*400000000000^4007 ≤ 173129157307^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132570657 10000000000 173129157307 400000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732500523/10000000000 : ℝ)^5031 ≤ (2767287270827/25000000000000 : ℝ)^4007 := by
    have hnat : (1732500523 : ℕ)^5031*25000000000000^4007 ≤ 2767287270827^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732500523 10000000000 2767287270827 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354841819/10000000000 : ℝ), (5132570657/10000000000 : ℝ), (-1732500523/10000000000 : ℝ)] ![(4564856157177/10000000000000 : ℝ), (173129157307/400000000000 : ℝ), (2767287270827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354841819/10000000000 : ℝ)|^5031 ≤ (4564856157177/10000000000000 : ℝ)^4007
        have hw : |(5354841819/10000000000 : ℝ)|=(5354841819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132570657/10000000000 : ℝ)|^5031 ≤ (173129157307/400000000000 : ℝ)^4007
        have hw : |(5132570657/10000000000 : ℝ)|=(5132570657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1732500523/10000000000 : ℝ)|^5031 ≤ (2767287270827/25000000000000 : ℝ)^4007
        have hw : |(-1732500523/10000000000 : ℝ)|=(1732500523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s4_3 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4150909761/10000000000 : ℝ)*x 0 + (3688383343/10000000000 : ℝ)*x 1 + (4652266529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4150909761/10000000000 : ℝ)^5031 ≤ (4144467714723/12500000000000 : ℝ)^4007 := by
    have hnat : (4150909761 : ℕ)^5031*12500000000000^4007 ≤ 4144467714723^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150909761 10000000000 4144467714723 12500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688383343/10000000000 : ℝ)^5031 ≤ (14292552763101/50000000000000 : ℝ)^4007 := by
    have hnat : (3688383343 : ℕ)^5031*50000000000000^4007 ≤ 14292552763101^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688383343 10000000000 14292552763101 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4652266529/10000000000 : ℝ)^5031 ≤ (38259152733339/100000000000000 : ℝ)^4007 := by
    have hnat : (4652266529 : ℕ)^5031*100000000000000^4007 ≤ 38259152733339^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4652266529 10000000000 38259152733339 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4150909761/10000000000 : ℝ), (3688383343/10000000000 : ℝ), (4652266529/10000000000 : ℝ)] ![(4144467714723/12500000000000 : ℝ), (14292552763101/50000000000000 : ℝ), (38259152733339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4150909761/10000000000 : ℝ)|^5031 ≤ (4144467714723/12500000000000 : ℝ)^4007
        have hw : |(4150909761/10000000000 : ℝ)|=(4150909761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688383343/10000000000 : ℝ)|^5031 ≤ (14292552763101/50000000000000 : ℝ)^4007
        have hw : |(3688383343/10000000000 : ℝ)|=(3688383343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4652266529/10000000000 : ℝ)|^5031 ≤ (38259152733339/100000000000000 : ℝ)^4007
        have hw : |(4652266529/10000000000 : ℝ)|=(4652266529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s4_4 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-772639901/5000000000 : ℝ)*x 0 + (5136443243/10000000000 : ℝ)*x 1 + (686113819/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (772639901/5000000000 : ℝ)^5031 ≤ (1917721947643/20000000000000 : ℝ)^4007 := by
    have hnat : (772639901 : ℕ)^5031*20000000000000^4007 ≤ 1917721947643^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772639901 5000000000 1917721947643 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136443243/10000000000 : ℝ)^5031 ≤ (5415411984129/12500000000000 : ℝ)^4007 := by
    have hnat : (5136443243 : ℕ)^5031*12500000000000^4007 ≤ 5415411984129^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136443243 10000000000 5415411984129 12500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686113819/1250000000 : ℝ)^5031 ≤ (47088094370577/100000000000000 : ℝ)^4007 := by
    have hnat : (686113819 : ℕ)^5031*100000000000000^4007 ≤ 47088094370577^4007*1250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686113819 1250000000 47088094370577 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-772639901/5000000000 : ℝ), (5136443243/10000000000 : ℝ), (686113819/1250000000 : ℝ)] ![(1917721947643/20000000000000 : ℝ), (5415411984129/12500000000000 : ℝ), (47088094370577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-772639901/5000000000 : ℝ)|^5031 ≤ (1917721947643/20000000000000 : ℝ)^4007
        have hw : |(-772639901/5000000000 : ℝ)|=(772639901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136443243/10000000000 : ℝ)|^5031 ≤ (5415411984129/12500000000000 : ℝ)^4007
        have hw : |(5136443243/10000000000 : ℝ)|=(5136443243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686113819/1250000000 : ℝ)|^5031 ≤ (47088094370577/100000000000000 : ℝ)^4007
        have hw : |(686113819/1250000000 : ℝ)|=(686113819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s4_5 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629350787/5000000000 : ℝ)*x 0 + (-1376160791/10000000000 : ℝ)*x 1 + (2744455337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629350787/5000000000 : ℝ)^5031 ≤ (11155480078337/25000000000000 : ℝ)^4007 := by
    have hnat : (2629350787 : ℕ)^5031*25000000000000^4007 ≤ 11155480078337^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629350787 5000000000 11155480078337 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376160791/10000000000 : ℝ)^5031 ≤ (1657996799139/20000000000000 : ℝ)^4007 := by
    have hnat : (1376160791 : ℕ)^5031*20000000000000^4007 ≤ 1657996799139^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376160791 10000000000 1657996799139 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744455337/5000000000 : ℝ)^5031 ≤ (941761913693/2000000000000 : ℝ)^4007 := by
    have hnat : (2744455337 : ℕ)^5031*2000000000000^4007 ≤ 941761913693^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744455337 5000000000 941761913693 2000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629350787/5000000000 : ℝ), (-1376160791/10000000000 : ℝ), (2744455337/5000000000 : ℝ)] ![(11155480078337/25000000000000 : ℝ), (1657996799139/20000000000000 : ℝ), (941761913693/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629350787/5000000000 : ℝ)|^5031 ≤ (11155480078337/25000000000000 : ℝ)^4007
        have hw : |(2629350787/5000000000 : ℝ)|=(2629350787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1376160791/10000000000 : ℝ)|^5031 ≤ (1657996799139/20000000000000 : ℝ)^4007
        have hw : |(-1376160791/10000000000 : ℝ)|=(1376160791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744455337/5000000000 : ℝ)|^5031 ≤ (941761913693/2000000000000 : ℝ)^4007
        have hw : |(2744455337/5000000000 : ℝ)|=(2744455337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s4_6 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629350719/5000000000 : ℝ)*x 0 + (343056939/625000000 : ℝ)*x 1 + (-1376160483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629350719/5000000000 : ℝ)^5031 ≤ (44621918864431/100000000000000 : ℝ)^4007 := by
    have hnat : (2629350719 : ℕ)^5031*100000000000000^4007 ≤ 44621918864431^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629350719 5000000000 44621918864431 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343056939/625000000 : ℝ)^5031 ≤ (23544049727267/50000000000000 : ℝ)^4007 := by
    have hnat : (343056939 : ℕ)^5031*50000000000000^4007 ≤ 23544049727267^4007*625000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343056939 625000000 23544049727267 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376160483/10000000000 : ℝ)^5031 ≤ (1657996333231/20000000000000 : ℝ)^4007 := by
    have hnat : (1376160483 : ℕ)^5031*20000000000000^4007 ≤ 1657996333231^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376160483 10000000000 1657996333231 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629350719/5000000000 : ℝ), (343056939/625000000 : ℝ), (-1376160483/10000000000 : ℝ)] ![(44621918864431/100000000000000 : ℝ), (23544049727267/50000000000000 : ℝ), (1657996333231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629350719/5000000000 : ℝ)|^5031 ≤ (44621918864431/100000000000000 : ℝ)^4007
        have hw : |(2629350719/5000000000 : ℝ)|=(2629350719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343056939/625000000 : ℝ)|^5031 ≤ (23544049727267/50000000000000 : ℝ)^4007
        have hw : |(343056939/625000000 : ℝ)|=(343056939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1376160483/10000000000 : ℝ)|^5031 ≤ (1657996333231/20000000000000 : ℝ)^4007
        have hw : |(-1376160483/10000000000 : ℝ)|=(1376160483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_s4_7 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4151367797/10000000000 : ℝ)*x 0 + (464190687/1000000000 : ℝ)*x 1 + (3698897211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151367797/10000000000 : ℝ)^5031 ≤ (3316033534943/10000000000000 : ℝ)^4007 := by
    have hnat : (4151367797 : ℕ)^5031*10000000000000^4007 ≤ 3316033534943^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151367797 10000000000 3316033534943 10000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464190687/1000000000 : ℝ)^5031 ≤ (7630443169183/20000000000000 : ℝ)^4007 := by
    have hnat : (464190687 : ℕ)^5031*20000000000000^4007 ≤ 7630443169183^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464190687 1000000000 7630443169183 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3698897211/10000000000 : ℝ)^5031 ≤ (28687448795451/100000000000000 : ℝ)^4007 := by
    have hnat : (3698897211 : ℕ)^5031*100000000000000^4007 ≤ 28687448795451^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698897211 10000000000 28687448795451 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151367797/10000000000 : ℝ), (464190687/1000000000 : ℝ), (3698897211/10000000000 : ℝ)] ![(3316033534943/10000000000000 : ℝ), (7630443169183/20000000000000 : ℝ), (28687448795451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151367797/10000000000 : ℝ)|^5031 ≤ (3316033534943/10000000000000 : ℝ)^4007
        have hw : |(4151367797/10000000000 : ℝ)|=(4151367797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(464190687/1000000000 : ℝ)|^5031 ≤ (7630443169183/20000000000000 : ℝ)^4007
        have hw : |(464190687/1000000000 : ℝ)|=(464190687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3698897211/10000000000 : ℝ)|^5031 ≤ (28687448795451/100000000000000 : ℝ)^4007
        have hw : |(3698897211/10000000000 : ℝ)|=(3698897211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1676_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3467/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9681/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17333/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3467/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3467/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3467/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3467/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3467/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3467/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9679/100000 : ℝ) ^ (5023/1024 : ℝ) ≤ (529896736870099/50000000000000000000 : ℝ) := by
    have hpowers : (9679/100000 : ℝ)^5023 ≤ (529896736870099/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9679 : ℕ)^5023*50000000000000000000^1024 ≤ 529896736870099^1024*100000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9679 100000 529896736870099 50000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9679/100000 : ℝ)) (X := (529896736870099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3467/20000 : ℝ) ^ (5023/1024 : ℝ) ≤ (3696096942275651/20000000000000000000 : ℝ) := by
    have hpowers : (3467/20000 : ℝ)^5023 ≤ (3696096942275651/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3467 : ℕ)^5023*20000000000000000000^1024 ≤ 3696096942275651^1024*20000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3467 20000 3696096942275651 20000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3467/20000 : ℝ)) (X := (3696096942275651/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000529896736870099/25000000000000000000 : ℝ) ≤ (1000004321000839/1000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (25000529896736870099/25000000000000000000 : ℝ)^1024 ≤ (1000004321000839/1000000000000000 : ℝ)^5023 := by
      have hnat : (25000529896736870099 : ℕ)^1024*1000000000000000^5023 ≤ 1000004321000839^5023*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000529896736870099 25000000000000000000 1000004321000839 1000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000004321000839/1000000000000000 : ℝ)) (X := (25000529896736870099/25000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019540278185118453/100000000000000000000 : ℝ) ≤ (10000398321494111/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (100019540278185118453/100000000000000000000 : ℝ)^1024 ≤ (10000398321494111/10000000000000000 : ℝ)^5023 := by
      have hnat : (100019540278185118453 : ℕ)^1024*10000000000000000^5023 ≤ 10000398321494111^5023*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019540278185118453 100000000000000000000 10000398321494111 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000398321494111/10000000000000000 : ℝ)) (X := (100019540278185118453/100000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003696096942275651/10000000000000000000 : ℝ) ≤ (1250094179122479/1250000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (10003696096942275651/10000000000000000000 : ℝ)^1024 ≤ (1250094179122479/1250000000000000 : ℝ)^5023 := by
      have hnat : (10003696096942275651 : ℕ)^1024*1250000000000000^5023 ≤ 1250094179122479^5023*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003696096942275651 10000000000000000000 1250094179122479 1250000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250094179122479/1250000000000000 : ℝ)) (X := (10003696096942275651/10000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(529896736870099/50000000000000000000 : ℝ) ≤ ((38276728283841823361/38280000000000000000 : ℝ)+2*(355111485721/765600000000000 : ℝ)*(9679/100000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (38276728283841823361/38280000000000000000 : ℝ)+2*(355111485721/765600000000000 : ℝ)*(9679/100000 : ℝ)=(1000004321000839/1000000000000000 : ℝ) by norm_num, show 1+2*(529896736870099/50000000000000000000 : ℝ)=(25000529896736870099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3696096942275651/20000000000000000000 : ℝ)+(529896736870099/50000000000000000000 : ℝ) ≤ ((38276728283841823361/38280000000000000000 : ℝ)+(355111485721/765600000000000 : ℝ)*((3467/20000 : ℝ)+(9679/100000 : ℝ)))^(5023/1024 : ℝ) := by
    rw [show (38276728283841823361/38280000000000000000 : ℝ)+(355111485721/765600000000000 : ℝ)*((3467/20000 : ℝ)+(9679/100000 : ℝ))=(10000398321494111/10000000000000000 : ℝ) by norm_num, show 1+(3696096942275651/20000000000000000000 : ℝ)+(529896736870099/50000000000000000000 : ℝ)=(100019540278185118453/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3696096942275651/20000000000000000000 : ℝ) ≤ ((38276728283841823361/38280000000000000000 : ℝ)+2*(355111485721/765600000000000 : ℝ)*(3467/20000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (38276728283841823361/38280000000000000000 : ℝ)+2*(355111485721/765600000000000 : ℝ)*(3467/20000 : ℝ)=(1250094179122479/1250000000000000 : ℝ) by norm_num, show 1+2*(3696096942275651/20000000000000000000 : ℝ)=(10003696096942275651/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38276728283841823361/38280000000000000000 : ℝ)*(X 1 0+X 2 0)+(355111485721/765600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (9679/100000 : ℝ)) (hi := (3467/20000 : ℝ)) (c := (38276728283841823361/38280000000000000000 : ℝ)) (alpha := (355111485721/765600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38276728283841823361/38280000000000000000 : ℝ)*(X 0 1+X 2 1)+(355111485721/765600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (9679/100000 : ℝ)) (hi := (3467/20000 : ℝ)) (c := (38276728283841823361/38280000000000000000 : ℝ)) (alpha := (355111485721/765600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38276728283841823361/38280000000000000000 : ℝ)*(X 0 2+X 1 2)+(355111485721/765600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (9679/100000 : ℝ)) (hi := (3467/20000 : ℝ)) (c := (38276728283841823361/38280000000000000000 : ℝ)) (alpha := (355111485721/765600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-61804361/400000000 : ℝ)*X 0 0+(1373210121/2500000000 : ℝ)*X 0 1+(641571373/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338710343/2500000000 : ℝ)*X 1 0+(-866250387/5000000000 : ℝ)*X 1 1+(128314273/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354841819/10000000000 : ℝ)*X 2 0+(5132570657/10000000000 : ℝ)*X 2 1+(-1732500523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4150909761/10000000000 : ℝ)*X 0 0+(3688383343/10000000000 : ℝ)*X 0 1+(4652266529/10000000000 : ℝ)*X 0 2+(4150909761/10000000000 : ℝ)*X 1 0+(3688383343/10000000000 : ℝ)*X 1 1+(4652266529/10000000000 : ℝ)*X 1 2+(4150909761/10000000000 : ℝ)*X 2 0+(3688383343/10000000000 : ℝ)*X 2 1+(4652266529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-772639901/5000000000 : ℝ)*X 0 0+(5136443243/10000000000 : ℝ)*X 0 1+(686113819/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629350787/5000000000 : ℝ)*X 1 0+(-1376160791/10000000000 : ℝ)*X 1 1+(2744455337/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629350719/5000000000 : ℝ)*X 2 0+(343056939/625000000 : ℝ)*X 2 1+(-1376160483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4151367797/10000000000 : ℝ)*X 0 0+(464190687/1000000000 : ℝ)*X 0 1+(3698897211/10000000000 : ℝ)*X 0 2+(4151367797/10000000000 : ℝ)*X 1 0+(464190687/1000000000 : ℝ)*X 1 1+(3698897211/10000000000 : ℝ)*X 1 2+(4151367797/10000000000 : ℝ)*X 2 0+(464190687/1000000000 : ℝ)*X 2 1+(3698897211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3015603582992888803808267233/638000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (538418559/100000000000000 : ℝ)*(base19) + (23565251/3125000000000 : ℝ)*(base23) + (4676237/50000000000000 : ℝ)*(lower2) + (162387287/100000000000000 : ℝ)*(upper5) + (1906592064913153/100000000000000 : ℝ)*(major0) + (1906592064913153/100000000000000 : ℝ)*(major1) + (1906592064913153/100000000000000 : ℝ)*(major2) + (693925736208231/25000000000000 : ℝ)*(sp0) + (2775709262427409/100000000000000 : ℝ)*(sp1) + (173481820401171/6250000000000 : ℝ)*(sp2) + (518736193434311/50000000000000 : ℝ)*(sp3) + (1733918461/25000000000000 : ℝ)*(sp4) + (12447/15625000000 : ℝ)*(sp5) + (852447933/50000000000000 : ℝ)*(sp7) + (129684261470561/12500000000000 : ℝ)*(f.failure) + (173481867531673/6250000000000 : ℝ)*(f.sum) + (238239153064633/38280000000000000000000000000 : ℝ)*base65 + (2640407733775217233/3828000000000000000000000000000000 : ℝ)*base67 + (4609318181656782767/3828000000000000000000000000000000 : ℝ)*base70 + (14757445528782767/3828000000000000000000000000000000 : ℝ)*base72 + (187313475876313/38280000000000000000000000000 : ℝ)*base73 + (33133454908984782767/3828000000000000000000000000000000 : ℝ)*base76 + (15175296117463217233/3828000000000000000000000000000000 : ℝ)*base77 + (7540917144256782767/3828000000000000000000000000000000 : ℝ)*base80 + (25632979346233/38280000000000000000000000000 : ℝ)*base81 + (2598061/1250000000000000000000 : ℝ)*base90 + (2598061/1250000000000000000000 : ℝ)*base92 + (2598061/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146537172114369245589621/12760000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1422683569/100000000000000 : ℝ)*(base19) + (888437169/50000000000000 : ℝ)*(base23) + (409636593/100000000000000 : ℝ)*(lower1) + (66690407/25000000000000 : ℝ)*(upper3) + (16377247/10000000000000 : ℝ)*(lower4) + (22252193/12500000000000 : ℝ)*(upper5) + (1948779015308019/100000000000000 : ℝ)*(major0) + (1948779015308019/100000000000000 : ℝ)*(major1) + (1948779015308019/100000000000000 : ℝ)*(major2) + (1270450521/20000000000000 : ℝ)*(sp2) + (2837127482302303/100000000000000 : ℝ)*(sp4) + (1418563029809367/50000000000000 : ℝ)*(sp5) + (8865997978673/312500000000 : ℝ)*(sp6) + (132553770688781/12500000000000 : ℝ)*(sp7) + (132553770688781/12500000000000 : ℝ)*(f.failure) + (2837127482302303/100000000000000 : ℝ)*(f.sum) + (23926890898233/12760000000000000000000000000 : ℝ)*base65 + (13040712085417406047/1276000000000000000000000000000000 : ℝ)*base68 + (1426030813762593953/1276000000000000000000000000000000 : ℝ)*base69 + (44539070442674593953/1276000000000000000000000000000000 : ℝ)*base71 + (36938889885927/12760000000000000000000000000 : ℝ)*base74 + (5250467513197406047/1276000000000000000000000000000000 : ℝ)*base76 + (475873021409406047/1276000000000000000000000000000000 : ℝ)*base78 + (8834659965686593953/1276000000000000000000000000000000 : ℝ)*base79 + (11288016691153/12760000000000000000000000000 : ℝ)*base81 + (1866281/1250000000000000000000 : ℝ)*base90 + (1866281/1250000000000000000000 : ℝ)*base92 + (1866281/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1676_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3467/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9681/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17333/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1676_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1676_box_0 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-239522601/2000000000 : ℝ)*x 0 + (679497349/1250000000 : ℝ)*x 1 + (5435975857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239522601/2000000000 : ℝ)^5031 ≤ (1740675151911/25000000000000 : ℝ)^4007 := by
    have hnat : (239522601 : ℕ)^5031*25000000000000^4007 ≤ 1740675151911^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239522601 2000000000 1740675151911 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679497349/1250000000 : ℝ)^5031 ≤ (5814833181933/12500000000000 : ℝ)^4007 := by
    have hnat : (679497349 : ℕ)^5031*12500000000000^4007 ≤ 5814833181933^4007*1250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679497349 1250000000 5814833181933 12500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435975857/10000000000 : ℝ)^5031 ≤ (9303726784097/20000000000000 : ℝ)^4007 := by
    have hnat : (5435975857 : ℕ)^5031*20000000000000^4007 ≤ 9303726784097^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435975857 10000000000 9303726784097 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239522601/2000000000 : ℝ), (679497349/1250000000 : ℝ), (5435975857/10000000000 : ℝ)] ![(1740675151911/25000000000000 : ℝ), (5814833181933/12500000000000 : ℝ), (9303726784097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239522601/2000000000 : ℝ)|^5031 ≤ (1740675151911/25000000000000 : ℝ)^4007
        have hw : |(-239522601/2000000000 : ℝ)|=(239522601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679497349/1250000000 : ℝ)|^5031 ≤ (5814833181933/12500000000000 : ℝ)^4007
        have hw : |(679497349/1250000000 : ℝ)|=(679497349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435975857/10000000000 : ℝ)|^5031 ≤ (9303726784097/20000000000000 : ℝ)^4007
        have hw : |(5435975857/10000000000 : ℝ)|=(5435975857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_1 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261302181/500000000 : ℝ)*x 0 + (-149610577/1000000000 : ℝ)*x 1 + (1358994593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261302181/500000000 : ℝ)^5031 ≤ (44274265389427/100000000000000 : ℝ)^4007 := by
    have hnat : (261302181 : ℕ)^5031*100000000000000^4007 ≤ 44274265389427^4007*500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261302181 500000000 44274265389427 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149610577/1000000000 : ℝ)^5031 ≤ (1841414730477/20000000000000 : ℝ)^4007 := by
    have hnat : (149610577 : ℕ)^5031*20000000000000^4007 ≤ 1841414730477^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149610577 1000000000 1841414730477 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358994593/2500000000 : ℝ)^5031 ≤ (5814832617849/12500000000000 : ℝ)^4007 := by
    have hnat : (1358994593 : ℕ)^5031*12500000000000^4007 ≤ 5814832617849^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358994593 2500000000 5814832617849 12500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261302181/500000000 : ℝ), (-149610577/1000000000 : ℝ), (1358994593/2500000000 : ℝ)] ![(44274265389427/100000000000000 : ℝ), (1841414730477/20000000000000 : ℝ), (5814832617849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261302181/500000000 : ℝ)|^5031 ≤ (44274265389427/100000000000000 : ℝ)^4007
        have hw : |(261302181/500000000 : ℝ)|=(261302181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149610577/1000000000 : ℝ)|^5031 ≤ (1841414730477/20000000000000 : ℝ)^4007
        have hw : |(-149610577/1000000000 : ℝ)|=(149610577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358994593/2500000000 : ℝ)|^5031 ≤ (5814832617849/12500000000000 : ℝ)^4007
        have hw : |(1358994593/2500000000 : ℝ)|=(1358994593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_2 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226044357/10000000000 : ℝ)*x 0 + (169874291/312500000 : ℝ)*x 1 + (-149610623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226044357/10000000000 : ℝ)^5031 ≤ (4427427322879/10000000000000 : ℝ)^4007 := by
    have hnat : (5226044357 : ℕ)^5031*10000000000000^4007 ≤ 4427427322879^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226044357 10000000000 4427427322879 10000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169874291/312500000 : ℝ)^5031 ≤ (11629662388417/25000000000000 : ℝ)^4007 := by
    have hnat : (169874291 : ℕ)^5031*25000000000000^4007 ≤ 11629662388417^4007*312500000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169874291 312500000 11629662388417 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149610623/1000000000 : ℝ)^5031 ≤ (9207077206669/100000000000000 : ℝ)^4007 := by
    have hnat : (149610623 : ℕ)^5031*100000000000000^4007 ≤ 9207077206669^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149610623 1000000000 9207077206669 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226044357/10000000000 : ℝ), (169874291/312500000 : ℝ), (-149610623/1000000000 : ℝ)] ![(4427427322879/10000000000000 : ℝ), (11629662388417/25000000000000 : ℝ), (9207077206669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226044357/10000000000 : ℝ)|^5031 ≤ (4427427322879/10000000000000 : ℝ)^4007
        have hw : |(5226044357/10000000000 : ℝ)|=(5226044357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169874291/312500000 : ℝ)|^5031 ≤ (11629662388417/25000000000000 : ℝ)^4007
        have hw : |(169874291/312500000 : ℝ)|=(169874291/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-149610623/1000000000 : ℝ)|^5031 ≤ (9207077206669/100000000000000 : ℝ)^4007
        have hw : |(-149610623/1000000000 : ℝ)|=(149610623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_3 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4537346551/10000000000 : ℝ)*x 0 + (3981110261/10000000000 : ℝ)*x 1 + (796221713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4537346551/10000000000 : ℝ)^5031 ≤ (18538164804469/50000000000000 : ℝ)^4007 := by
    have hnat : (4537346551 : ℕ)^5031*50000000000000^4007 ≤ 18538164804469^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537346551 10000000000 18538164804469 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3981110261/10000000000 : ℝ)^5031 ≤ (31461843598817/100000000000000 : ℝ)^4007 := by
    have hnat : (3981110261 : ℕ)^5031*100000000000000^4007 ≤ 31461843598817^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3981110261 10000000000 31461843598817 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796221713/2000000000 : ℝ)^5031 ≤ (31461826770497/100000000000000 : ℝ)^4007 := by
    have hnat : (796221713 : ℕ)^5031*100000000000000^4007 ≤ 31461826770497^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796221713 2000000000 31461826770497 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4537346551/10000000000 : ℝ), (3981110261/10000000000 : ℝ), (796221713/2000000000 : ℝ)] ![(18538164804469/50000000000000 : ℝ), (31461843598817/100000000000000 : ℝ), (31461826770497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4537346551/10000000000 : ℝ)|^5031 ≤ (18538164804469/50000000000000 : ℝ)^4007
        have hw : |(4537346551/10000000000 : ℝ)|=(4537346551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3981110261/10000000000 : ℝ)|^5031 ≤ (31461843598817/100000000000000 : ℝ)^4007
        have hw : |(3981110261/10000000000 : ℝ)|=(3981110261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796221713/2000000000 : ℝ)|^5031 ≤ (31461826770497/100000000000000 : ℝ)^4007
        have hw : |(796221713/2000000000 : ℝ)|=(796221713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_4 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913788593/10000000000 : ℝ)*x 0 + (32341869/62500000 : ℝ)*x 1 + (2587349717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913788593/10000000000 : ℝ)^5031 ≤ (2508476062231/20000000000000 : ℝ)^4007 := by
    have hnat : (1913788593 : ℕ)^5031*20000000000000^4007 ≤ 2508476062231^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913788593 10000000000 2508476062231 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32341869/62500000 : ℝ)^5031 ≤ (683262620983/1562500000000 : ℝ)^4007 := by
    have hnat : (32341869 : ℕ)^5031*1562500000000^4007 ≤ 683262620983^4007*62500000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32341869 62500000 683262620983 1562500000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587349717/5000000000 : ℝ)^5031 ≤ (43728811923273/100000000000000 : ℝ)^4007 := by
    have hnat : (2587349717 : ℕ)^5031*100000000000000^4007 ≤ 43728811923273^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587349717 5000000000 43728811923273 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913788593/10000000000 : ℝ), (32341869/62500000 : ℝ), (2587349717/5000000000 : ℝ)] ![(2508476062231/20000000000000 : ℝ), (683262620983/1562500000000 : ℝ), (43728811923273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913788593/10000000000 : ℝ)|^5031 ≤ (2508476062231/20000000000000 : ℝ)^4007
        have hw : |(-1913788593/10000000000 : ℝ)|=(1913788593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32341869/62500000 : ℝ)|^5031 ≤ (683262620983/1562500000000 : ℝ)^4007
        have hw : |(32341869/62500000 : ℝ)|=(32341869/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587349717/5000000000 : ℝ)|^5031 ≤ (43728811923273/100000000000000 : ℝ)^4007
        have hw : |(2587349717/5000000000 : ℝ)|=(2587349717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_5 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404744053/10000000000 : ℝ)*x 0 + (-201128939/1250000000 : ℝ)*x 1 + (5174699061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404744053/10000000000 : ℝ)^5031 ≤ (1443228496759/3125000000000 : ℝ)^4007 := by
    have hnat : (5404744053 : ℕ)^5031*3125000000000^4007 ≤ 1443228496759^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404744053 10000000000 1443228496759 3125000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201128939/1250000000 : ℝ)^5031 ≤ (2017576023009/20000000000000 : ℝ)^4007 := by
    have hnat : (201128939 : ℕ)^5031*20000000000000^4007 ≤ 2017576023009^4007*1250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201128939 1250000000 2017576023009 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174699061/10000000000 : ℝ)^5031 ≤ (10932201991431/25000000000000 : ℝ)^4007 := by
    have hnat : (5174699061 : ℕ)^5031*25000000000000^4007 ≤ 10932201991431^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174699061 10000000000 10932201991431 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404744053/10000000000 : ℝ), (-201128939/1250000000 : ℝ), (5174699061/10000000000 : ℝ)] ![(1443228496759/3125000000000 : ℝ), (2017576023009/20000000000000 : ℝ), (10932201991431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404744053/10000000000 : ℝ)|^5031 ≤ (1443228496759/3125000000000 : ℝ)^4007
        have hw : |(5404744053/10000000000 : ℝ)|=(5404744053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201128939/1250000000 : ℝ)|^5031 ≤ (2017576023009/20000000000000 : ℝ)^4007
        have hw : |(-201128939/1250000000 : ℝ)|=(201128939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174699061/10000000000 : ℝ)|^5031 ≤ (10932201991431/25000000000000 : ℝ)^4007
        have hw : |(5174699061/10000000000 : ℝ)|=(5174699061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_6 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404743943/10000000000 : ℝ)*x 0 + (2587349593/5000000000 : ℝ)*x 1 + (-321806299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404743943/10000000000 : ℝ)^5031 ≤ (46183310716137/100000000000000 : ℝ)^4007 := by
    have hnat : (5404743943 : ℕ)^5031*100000000000000^4007 ≤ 46183310716137^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404743943 10000000000 46183310716137 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587349593/5000000000 : ℝ)^5031 ≤ (2186440464599/5000000000000 : ℝ)^4007 := by
    have hnat : (2587349593 : ℕ)^5031*5000000000000^4007 ≤ 2186440464599^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587349593 5000000000 2186440464599 5000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321806299/2000000000 : ℝ)^5031 ≤ (403515199249/4000000000000 : ℝ)^4007 := by
    have hnat : (321806299 : ℕ)^5031*4000000000000^4007 ≤ 403515199249^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321806299 2000000000 403515199249 4000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404743943/10000000000 : ℝ), (2587349593/5000000000 : ℝ), (-321806299/2000000000 : ℝ)] ![(46183310716137/100000000000000 : ℝ), (2186440464599/5000000000000 : ℝ), (403515199249/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404743943/10000000000 : ℝ)|^5031 ≤ (46183310716137/100000000000000 : ℝ)^4007
        have hw : |(5404743943/10000000000 : ℝ)|=(5404743943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587349593/5000000000 : ℝ)|^5031 ≤ (2186440464599/5000000000000 : ℝ)^4007
        have hw : |(2587349593/5000000000 : ℝ)|=(2587349593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321806299/2000000000 : ℝ)|^5031 ≤ (403515199249/4000000000000 : ℝ)^4007
        have hw : |(-321806299/2000000000 : ℝ)|=(321806299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_7 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3750694233/10000000000 : ℝ)*x 0 + (2186773321/5000000000 : ℝ)*x 1 + (218677351/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3750694233/10000000000 : ℝ)^5031 ≤ (912272812389/3125000000000 : ℝ)^4007 := by
    have hnat : (3750694233 : ℕ)^5031*3125000000000^4007 ≤ 912272812389^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3750694233 10000000000 912272812389 3125000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186773321/5000000000 : ℝ)^5031 ≤ (17701816536183/50000000000000 : ℝ)^4007 := by
    have hnat : (2186773321 : ℕ)^5031*50000000000000^4007 ≤ 17701816536183^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186773321 5000000000 17701816536183 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218677351/500000000 : ℝ)^5031 ≤ (1770181845711/5000000000000 : ℝ)^4007 := by
    have hnat : (218677351 : ℕ)^5031*5000000000000^4007 ≤ 1770181845711^4007*500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218677351 500000000 1770181845711 5000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3750694233/10000000000 : ℝ), (2186773321/5000000000 : ℝ), (218677351/500000000 : ℝ)] ![(912272812389/3125000000000 : ℝ), (17701816536183/50000000000000 : ℝ), (1770181845711/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3750694233/10000000000 : ℝ)|^5031 ≤ (912272812389/3125000000000 : ℝ)^4007
        have hw : |(3750694233/10000000000 : ℝ)|=(3750694233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2186773321/5000000000 : ℝ)|^5031 ≤ (17701816536183/50000000000000 : ℝ)^4007
        have hw : |(2186773321/5000000000 : ℝ)|=(2186773321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218677351/500000000 : ℝ)|^5031 ≤ (1770181845711/5000000000000 : ℝ)^4007
        have hw : |(218677351/500000000 : ℝ)|=(218677351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_8 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220054763/1250000000 : ℝ)*x 0 + (498376451/1000000000 : ℝ)*x 1 + (5480141079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220054763/1250000000 : ℝ)^5031 ≤ (11293720778823/100000000000000 : ℝ)^4007 := by
    have hnat : (220054763 : ℕ)^5031*100000000000000^4007 ≤ 11293720778823^4007*1250000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220054763 1250000000 11293720778823 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498376451/1000000000 : ℝ)^5031 ≤ (20856311197367/50000000000000 : ℝ)^4007 := by
    have hnat : (498376451 : ℕ)^5031*50000000000000^4007 ≤ 20856311197367^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498376451 1000000000 20856311197367 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480141079/10000000000 : ℝ)^5031 ≤ (9398731363373/20000000000000 : ℝ)^4007 := by
    have hnat : (5480141079 : ℕ)^5031*20000000000000^4007 ≤ 9398731363373^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480141079 10000000000 9398731363373 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220054763/1250000000 : ℝ), (498376451/1000000000 : ℝ), (5480141079/10000000000 : ℝ)] ![(11293720778823/100000000000000 : ℝ), (20856311197367/50000000000000 : ℝ), (9398731363373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220054763/1250000000 : ℝ)|^5031 ≤ (11293720778823/100000000000000 : ℝ)^4007
        have hw : |(-220054763/1250000000 : ℝ)|=(220054763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(498376451/1000000000 : ℝ)|^5031 ≤ (20856311197367/50000000000000 : ℝ)^4007
        have hw : |(498376451/1000000000 : ℝ)|=(498376451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480141079/10000000000 : ℝ)|^5031 ≤ (9398731363373/20000000000000 : ℝ)^4007
        have hw : |(5480141079/10000000000 : ℝ)|=(5480141079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_9 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039168717/2000000000 : ℝ)*x 0 + (-369035279/2500000000 : ℝ)*x 1 + (5480140811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039168717/2000000000 : ℝ)^5031 ≤ (879065389617/2000000000000 : ℝ)^4007 := by
    have hnat : (1039168717 : ℕ)^5031*2000000000000^4007 ≤ 879065389617^4007*2000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039168717 2000000000 879065389617 2000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369035279/2500000000 : ℝ)^5031 ≤ (9053076580359/100000000000000 : ℝ)^4007 := by
    have hnat : (369035279 : ℕ)^5031*100000000000000^4007 ≤ 9053076580359^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369035279 2500000000 9053076580359 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480140811/10000000000 : ℝ)^5031 ≤ (4699365393139/10000000000000 : ℝ)^4007 := by
    have hnat : (5480140811 : ℕ)^5031*10000000000000^4007 ≤ 4699365393139^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480140811 10000000000 4699365393139 10000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039168717/2000000000 : ℝ), (-369035279/2500000000 : ℝ), (5480140811/10000000000 : ℝ)] ![(879065389617/2000000000000 : ℝ), (9053076580359/100000000000000 : ℝ), (4699365393139/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039168717/2000000000 : ℝ)|^5031 ≤ (879065389617/2000000000000 : ℝ)^4007
        have hw : |(1039168717/2000000000 : ℝ)|=(1039168717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369035279/2500000000 : ℝ)|^5031 ≤ (9053076580359/100000000000000 : ℝ)^4007
        have hw : |(-369035279/2500000000 : ℝ)|=(369035279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480140811/10000000000 : ℝ)|^5031 ≤ (4699365393139/10000000000000 : ℝ)^4007
        have hw : |(5480140811/10000000000 : ℝ)|=(5480140811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_10 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195844147/10000000000 : ℝ)*x 0 + (274007029/500000000 : ℝ)*x 1 + (-1476140663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195844147/10000000000 : ℝ)^5031 ≤ (10988318862479/25000000000000 : ℝ)^4007 := by
    have hnat : (5195844147 : ℕ)^5031*25000000000000^4007 ≤ 10988318862479^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195844147 10000000000 10988318862479 25000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274007029/500000000 : ℝ)^5031 ≤ (46993651444283/100000000000000 : ℝ)^4007 := by
    have hnat : (274007029 : ℕ)^5031*100000000000000^4007 ≤ 46993651444283^4007*500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274007029 500000000 46993651444283 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1476140663/10000000000 : ℝ)^5031 ≤ (4526536546079/50000000000000 : ℝ)^4007 := by
    have hnat : (1476140663 : ℕ)^5031*50000000000000^4007 ≤ 4526536546079^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476140663 10000000000 4526536546079 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195844147/10000000000 : ℝ), (274007029/500000000 : ℝ), (-1476140663/10000000000 : ℝ)] ![(10988318862479/25000000000000 : ℝ), (46993651444283/100000000000000 : ℝ), (4526536546079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195844147/10000000000 : ℝ)|^5031 ≤ (10988318862479/25000000000000 : ℝ)^4007
        have hw : |(5195844147/10000000000 : ℝ)|=(5195844147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274007029/500000000 : ℝ)|^5031 ≤ (46993651444283/100000000000000 : ℝ)^4007
        have hw : |(274007029/500000000 : ℝ)|=(274007029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1476140663/10000000000 : ℝ)|^5031 ≤ (4526536546079/50000000000000 : ℝ)^4007
        have hw : |(-1476140663/10000000000 : ℝ)|=(1476140663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_11 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4665253841/10000000000 : ℝ)*x 0 + (1957301317/5000000000 : ℝ)*x 1 + (3914603591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4665253841/10000000000 : ℝ)^5031 ≤ (38393299369931/100000000000000 : ℝ)^4007 := by
    have hnat : (4665253841 : ℕ)^5031*100000000000000^4007 ≤ 38393299369931^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4665253841 10000000000 38393299369931 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957301317/5000000000 : ℝ)^5031 ≤ (6160669116593/20000000000000 : ℝ)^4007 := by
    have hnat : (1957301317 : ℕ)^5031*20000000000000^4007 ≤ 6160669116593^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957301317 5000000000 6160669116593 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3914603591/10000000000 : ℝ)^5031 ≤ (3080335503787/10000000000000 : ℝ)^4007 := by
    have hnat : (3914603591 : ℕ)^5031*10000000000000^4007 ≤ 3080335503787^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3914603591 10000000000 3080335503787 10000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4665253841/10000000000 : ℝ), (1957301317/5000000000 : ℝ), (3914603591/10000000000 : ℝ)] ![(38393299369931/100000000000000 : ℝ), (6160669116593/20000000000000 : ℝ), (3080335503787/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4665253841/10000000000 : ℝ)|^5031 ≤ (38393299369931/100000000000000 : ℝ)^4007
        have hw : |(4665253841/10000000000 : ℝ)|=(4665253841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1957301317/5000000000 : ℝ)|^5031 ≤ (6160669116593/20000000000000 : ℝ)^4007
        have hw : |(1957301317/5000000000 : ℝ)|=(1957301317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3914603591/10000000000 : ℝ)|^5031 ≤ (3080335503787/10000000000000 : ℝ)^4007
        have hw : |(3914603591/10000000000 : ℝ)|=(3914603591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_12 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-42083933/312500000 : ℝ)*x 0 + (2808541397/5000000000 : ℝ)*x 1 + (514930917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42083933/312500000 : ℝ)^5031 ≤ (4033832706199/50000000000000 : ℝ)^4007 := by
    have hnat : (42083933 : ℕ)^5031*50000000000000^4007 ≤ 4033832706199^4007*312500000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42083933 312500000 4033832706199 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2808541397/5000000000 : ℝ)^5031 ≤ (48472745586561/100000000000000 : ℝ)^4007 := by
    have hnat : (2808541397 : ℕ)^5031*100000000000000^4007 ≤ 48472745586561^4007*5000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808541397 5000000000 48472745586561 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514930917/1000000000 : ℝ)^5031 ≤ (43459588996347/100000000000000 : ℝ)^4007 := by
    have hnat : (514930917 : ℕ)^5031*100000000000000^4007 ≤ 43459588996347^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514930917 1000000000 43459588996347 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42083933/312500000 : ℝ), (2808541397/5000000000 : ℝ), (514930917/1000000000 : ℝ)] ![(4033832706199/50000000000000 : ℝ), (48472745586561/100000000000000 : ℝ), (43459588996347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42083933/312500000 : ℝ)|^5031 ≤ (4033832706199/50000000000000 : ℝ)^4007
        have hw : |(-42083933/312500000 : ℝ)|=(42083933/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2808541397/5000000000 : ℝ)|^5031 ≤ (48472745586561/100000000000000 : ℝ)^4007
        have hw : |(2808541397/5000000000 : ℝ)|=(2808541397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514930917/1000000000 : ℝ)|^5031 ≤ (43459588996347/100000000000000 : ℝ)^4007
        have hw : |(514930917/1000000000 : ℝ)|=(514930917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_13 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422134579/10000000000 : ℝ)*x 0 + (-1619512739/10000000000 : ℝ)*x 1 + (1287327093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422134579/10000000000 : ℝ)^5031 ≤ (1159249133539/2500000000000 : ℝ)^4007 := by
    have hnat : (5422134579 : ℕ)^5031*2500000000000^4007 ≤ 1159249133539^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422134579 10000000000 1159249133539 2500000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1619512739/10000000000 : ℝ)^5031 ≤ (2034090818739/20000000000000 : ℝ)^4007 := by
    have hnat : (1619512739 : ℕ)^5031*20000000000000^4007 ≤ 2034090818739^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619512739 10000000000 2034090818739 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287327093/2500000000 : ℝ)^5031 ≤ (21729790270081/50000000000000 : ℝ)^4007 := by
    have hnat : (1287327093 : ℕ)^5031*50000000000000^4007 ≤ 21729790270081^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287327093 2500000000 21729790270081 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422134579/10000000000 : ℝ), (-1619512739/10000000000 : ℝ), (1287327093/2500000000 : ℝ)] ![(1159249133539/2500000000000 : ℝ), (2034090818739/20000000000000 : ℝ), (21729790270081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422134579/10000000000 : ℝ)|^5031 ≤ (1159249133539/2500000000000 : ℝ)^4007
        have hw : |(5422134579/10000000000 : ℝ)|=(5422134579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1619512739/10000000000 : ℝ)|^5031 ≤ (2034090818739/20000000000000 : ℝ)^4007
        have hw : |(-1619512739/10000000000 : ℝ)|=(1619512739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287327093/2500000000 : ℝ)|^5031 ≤ (21729790270081/50000000000000 : ℝ)^4007
        have hw : |(1287327093/2500000000 : ℝ)|=(1287327093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_14 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422134517/10000000000 : ℝ)*x 0 + (5149308653/10000000000 : ℝ)*x 1 + (-12652441/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422134517/10000000000 : ℝ)^5031 ≤ (23184982337919/50000000000000 : ℝ)^4007 := by
    have hnat : (5422134517 : ℕ)^5031*50000000000000^4007 ≤ 23184982337919^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422134517 10000000000 23184982337919 50000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149308653/10000000000 : ℝ)^5031 ≤ (43459583517841/100000000000000 : ℝ)^4007 := by
    have hnat : (5149308653 : ℕ)^5031*100000000000000^4007 ≤ 43459583517841^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149308653 10000000000 43459583517841 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12652441/78125000 : ℝ)^5031 ≤ (10170451799217/100000000000000 : ℝ)^4007 := by
    have hnat : (12652441 : ℕ)^5031*100000000000000^4007 ≤ 10170451799217^4007*78125000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12652441 78125000 10170451799217 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422134517/10000000000 : ℝ), (5149308653/10000000000 : ℝ), (-12652441/78125000 : ℝ)] ![(23184982337919/50000000000000 : ℝ), (43459583517841/100000000000000 : ℝ), (10170451799217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422134517/10000000000 : ℝ)|^5031 ≤ (23184982337919/50000000000000 : ℝ)^4007
        have hw : |(5422134517/10000000000 : ℝ)|=(5422134517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149308653/10000000000 : ℝ)|^5031 ≤ (43459583517841/100000000000000 : ℝ)^4007
        have hw : |(5149308653/10000000000 : ℝ)|=(5149308653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12652441/78125000 : ℝ)|^5031 ≤ (10170451799217/100000000000000 : ℝ)^4007
        have hw : |(-12652441/78125000 : ℝ)|=(12652441/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1676_box_15 (p : ℝ) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3671270993/10000000000 : ℝ)*x 0 + (1102896201/2500000000 : ℝ)*x 1 + (441158217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3671270993/10000000000 : ℝ)^5031 ≤ (5683738252779/20000000000000 : ℝ)^4007 := by
    have hnat : (3671270993 : ℕ)^5031*20000000000000^4007 ≤ 5683738252779^4007*10000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3671270993 10000000000 5683738252779 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102896201/2500000000 : ℝ)^5031 ≤ (7158133553729/20000000000000 : ℝ)^4007 := by
    have hnat : (1102896201 : ℕ)^5031*20000000000000^4007 ≤ 7158133553729^4007*2500000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102896201 2500000000 7158133553729 20000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441158217/1000000000 : ℝ)^5031 ≤ (35790640938323/100000000000000 : ℝ)^4007 := by
    have hnat : (441158217 : ℕ)^5031*100000000000000^4007 ≤ 35790640938323^4007*1000000000^5031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441158217 1000000000 35790640938323 100000000000000 5031 4007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5031/1024 : ℝ)) 5031 4007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3671270993/10000000000 : ℝ), (1102896201/2500000000 : ℝ), (441158217/1000000000 : ℝ)] ![(5683738252779/20000000000000 : ℝ), (7158133553729/20000000000000 : ℝ), (35790640938323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3671270993/10000000000 : ℝ)|^5031 ≤ (5683738252779/20000000000000 : ℝ)^4007
        have hw : |(3671270993/10000000000 : ℝ)|=(3671270993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102896201/2500000000 : ℝ)|^5031 ≤ (7158133553729/20000000000000 : ℝ)^4007
        have hw : |(1102896201/2500000000 : ℝ)|=(1102896201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441158217/1000000000 : ℝ)|^5031 ≤ (35790640938323/100000000000000 : ℝ)^4007
        have hw : |(441158217/1000000000 : ℝ)|=(441158217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1676_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17333/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9681/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16617/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11519/20000 : ℝ) ∧ (10037/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (562/625 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17333/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9681/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17333/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9681/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17333/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9681/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17333/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9681/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17333/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9681/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17333/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9681/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9681/100000 : ℝ) ^ (5023/1024 : ℝ) ≤ (530434052162217/50000000000000000000 : ℝ) := by
    have hpowers : (9681/100000 : ℝ)^5023 ≤ (530434052162217/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9681 : ℕ)^5023*50000000000000000000^1024 ≤ 530434052162217^1024*100000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9681 100000 530434052162217 50000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9681/100000 : ℝ)) (X := (530434052162217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17333/100000 : ℝ) ^ (5023/1024 : ℝ) ≤ (369400564926681/2000000000000000000 : ℝ) := by
    have hpowers : (17333/100000 : ℝ)^5023 ≤ (369400564926681/2000000000000000000 : ℝ)^1024 := by
      have hnat : (17333 : ℕ)^5023*2000000000000000000^1024 ≤ 369400564926681^1024*100000^5023 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17333 100000 369400564926681 2000000000000000000 5023 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17333/100000 : ℝ)) (X := (369400564926681/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000530434052162217/25000000000000000000 : ℝ) ≤ (10000043253822969/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (25000530434052162217/25000000000000000000 : ℝ)^1024 ≤ (10000043253822969/10000000000000000 : ℝ)^5023 := by
      have hnat : (25000530434052162217 : ℕ)^1024*10000000000000000^5023 ≤ 10000043253822969^5023*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000530434052162217 25000000000000000000 10000043253822969 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000043253822969/10000000000000000 : ℝ)) (X := (25000530434052162217/25000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004882724087664621/25000000000000000000 : ℝ) ≤ (15625622078537/15625000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (25004882724087664621/25000000000000000000 : ℝ)^1024 ≤ (15625622078537/15625000000000 : ℝ)^5023 := by
      have hnat : (25004882724087664621 : ℕ)^1024*15625000000000^5023 ≤ 15625622078537^5023*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004882724087664621 25000000000000000000 15625622078537 15625000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15625622078537/15625000000000 : ℝ)) (X := (25004882724087664621/25000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000369400564926681/1000000000000000000 : ℝ) ≤ (10000753006704391/10000000000000000 : ℝ) ^ (5023/1024 : ℝ) := by
    have hpowers : (1000369400564926681/1000000000000000000 : ℝ)^1024 ≤ (10000753006704391/10000000000000000 : ℝ)^5023 := by
      have hnat : (1000369400564926681 : ℕ)^1024*10000000000000000^5023 ≤ 10000753006704391^5023*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000369400564926681 1000000000000000000 10000753006704391 10000000000000000 1024 5023 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000753006704391/10000000000000000 : ℝ)) (X := (1000369400564926681/1000000000000000000 : ℝ)) (by norm_num) 5023 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(530434052162217/50000000000000000000 : ℝ) ≤ ((38256729930304156203/38260000000000000000 : ℝ)+2*(354876440711/765200000000000 : ℝ)*(9681/100000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (38256729930304156203/38260000000000000000 : ℝ)+2*(354876440711/765200000000000 : ℝ)*(9681/100000 : ℝ)=(10000043253822969/10000000000000000 : ℝ) by norm_num, show 1+2*(530434052162217/50000000000000000000 : ℝ)=(25000530434052162217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(369400564926681/2000000000000000000 : ℝ)+(530434052162217/50000000000000000000 : ℝ) ≤ ((38256729930304156203/38260000000000000000 : ℝ)+(354876440711/765200000000000 : ℝ)*((17333/100000 : ℝ)+(9681/100000 : ℝ)))^(5023/1024 : ℝ) := by
    rw [show (38256729930304156203/38260000000000000000 : ℝ)+(354876440711/765200000000000 : ℝ)*((17333/100000 : ℝ)+(9681/100000 : ℝ))=(15625622078537/15625000000000 : ℝ) by norm_num, show 1+(369400564926681/2000000000000000000 : ℝ)+(530434052162217/50000000000000000000 : ℝ)=(25004882724087664621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(369400564926681/2000000000000000000 : ℝ) ≤ ((38256729930304156203/38260000000000000000 : ℝ)+2*(354876440711/765200000000000 : ℝ)*(17333/100000 : ℝ))^(5023/1024 : ℝ) := by
    rw [show (38256729930304156203/38260000000000000000 : ℝ)+2*(354876440711/765200000000000 : ℝ)*(17333/100000 : ℝ)=(10000753006704391/10000000000000000 : ℝ) by norm_num, show 1+2*(369400564926681/2000000000000000000 : ℝ)=(1000369400564926681/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38256729930304156203/38260000000000000000 : ℝ)*(X 1 0+X 2 0)+(354876440711/765200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (9681/100000 : ℝ)) (hi := (17333/100000 : ℝ)) (c := (38256729930304156203/38260000000000000000 : ℝ)) (alpha := (354876440711/765200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38256729930304156203/38260000000000000000 : ℝ)*(X 0 1+X 2 1)+(354876440711/765200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (9681/100000 : ℝ)) (hi := (17333/100000 : ℝ)) (c := (38256729930304156203/38260000000000000000 : ℝ)) (alpha := (354876440711/765200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38256729930304156203/38260000000000000000 : ℝ)*(X 0 2+X 1 2)+(354876440711/765200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5023/1024 : ℝ)) (lo := (9681/100000 : ℝ)) (hi := (17333/100000 : ℝ)) (c := (38256729930304156203/38260000000000000000 : ℝ)) (alpha := (354876440711/765200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-239522601/2000000000 : ℝ)*X 0 0+(679497349/1250000000 : ℝ)*X 0 1+(5435975857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((261302181/500000000 : ℝ)*X 1 0+(-149610577/1000000000 : ℝ)*X 1 1+(1358994593/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5226044357/10000000000 : ℝ)*X 2 0+(169874291/312500000 : ℝ)*X 2 1+(-149610623/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4537346551/10000000000 : ℝ)*X 0 0+(3981110261/10000000000 : ℝ)*X 0 1+(796221713/2000000000 : ℝ)*X 0 2+(4537346551/10000000000 : ℝ)*X 1 0+(3981110261/10000000000 : ℝ)*X 1 1+(796221713/2000000000 : ℝ)*X 1 2+(4537346551/10000000000 : ℝ)*X 2 0+(3981110261/10000000000 : ℝ)*X 2 1+(796221713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1913788593/10000000000 : ℝ)*X 0 0+(32341869/62500000 : ℝ)*X 0 1+(2587349717/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5404744053/10000000000 : ℝ)*X 1 0+(-201128939/1250000000 : ℝ)*X 1 1+(5174699061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5404743943/10000000000 : ℝ)*X 2 0+(2587349593/5000000000 : ℝ)*X 2 1+(-321806299/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3750694233/10000000000 : ℝ)*X 0 0+(2186773321/5000000000 : ℝ)*X 0 1+(218677351/500000000 : ℝ)*X 0 2+(3750694233/10000000000 : ℝ)*X 1 0+(2186773321/5000000000 : ℝ)*X 1 1+(218677351/500000000 : ℝ)*X 1 2+(3750694233/10000000000 : ℝ)*X 2 0+(2186773321/5000000000 : ℝ)*X 2 1+(218677351/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-220054763/1250000000 : ℝ)*X 0 0+(498376451/1000000000 : ℝ)*X 0 1+(5480141079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1039168717/2000000000 : ℝ)*X 1 0+(-369035279/2500000000 : ℝ)*X 1 1+(5480140811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5195844147/10000000000 : ℝ)*X 2 0+(274007029/500000000 : ℝ)*X 2 1+(-1476140663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4665253841/10000000000 : ℝ)*X 0 0+(1957301317/5000000000 : ℝ)*X 0 1+(3914603591/10000000000 : ℝ)*X 0 2+(4665253841/10000000000 : ℝ)*X 1 0+(1957301317/5000000000 : ℝ)*X 1 1+(3914603591/10000000000 : ℝ)*X 1 2+(4665253841/10000000000 : ℝ)*X 2 0+(1957301317/5000000000 : ℝ)*X 2 1+(3914603591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-42083933/312500000 : ℝ)*X 0 0+(2808541397/5000000000 : ℝ)*X 0 1+(514930917/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5422134579/10000000000 : ℝ)*X 1 0+(-1619512739/10000000000 : ℝ)*X 1 1+(1287327093/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5422134517/10000000000 : ℝ)*X 2 0+(5149308653/10000000000 : ℝ)*X 2 1+(-12652441/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3671270993/10000000000 : ℝ)*X 0 0+(1102896201/2500000000 : ℝ)*X 0 1+(441158217/1000000000 : ℝ)*X 0 2+(3671270993/10000000000 : ℝ)*X 1 0+(1102896201/2500000000 : ℝ)*X 1 1+(441158217/1000000000 : ℝ)*X 1 2+(3671270993/10000000000 : ℝ)*X 2 0+(1102896201/2500000000 : ℝ)*X 2 1+(441158217/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1676_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16617/25000 : ℝ) ≤ (-1271478106704487293114695865949107/1913000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (347387/12500000000000 : ℝ)*(lower3) + (20473451/100000000000000 : ℝ)*(lower4) + (330559/1250000000000 : ℝ)*(upper5) + (1269155408652077/100000000000000 : ℝ)*(major0) + (1269155408652077/100000000000000 : ℝ)*(major1) + (1269155408652077/100000000000000 : ℝ)*(major2) + (2422415127/100000000000000 : ℝ)*(sp1) + (2417113857/100000000000000 : ℝ)*(sp2) + (236687363/50000000000000 : ℝ)*(sp3) + (467463039164281/25000000000000 : ℝ)*(sp4) + (934925590577047/50000000000000 : ℝ)*(sp5) + (467462796613841/25000000000000 : ℝ)*(sp6) + (345305893326159/50000000000000 : ℝ)*(sp7) + (45216003/3125000000000 : ℝ)*(sp12) + (172653065006761/25000000000000 : ℝ)*(f.failure) + (1869853603569221/100000000000000 : ℝ)*(f.sum) + (31994266483627/38260000000000000000000000000 : ℝ)*base65 + (1293162438149733631/3826000000000000000000000000000000 : ℝ)*base67 + (3672582981789733631/3826000000000000000000000000000000 : ℝ)*base69 + (17261323051066266369/3826000000000000000000000000000000 : ℝ)*base72 + (39269967446507/38260000000000000000000000000 : ℝ)*base73 + (21135778139702266369/3826000000000000000000000000000000 : ℝ)*base76 + (17824787555720266369/3826000000000000000000000000000000 : ℝ)*base78 + (19539059028554266369/3826000000000000000000000000000000 : ℝ)*base80 + (2535947039147/38260000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4134261/2500000000000000000000 : ℝ)*base90 + (4134261/2500000000000000000000 : ℝ)*base92 + (4134261/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11519/20000 : ℝ) ≤ (13772899304812921474137916363497/23912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (578093/50000000000000 : ℝ)*(lower1) + (5184107/6250000000000 : ℝ)*(lower2) + (178343221/100000000000000 : ℝ)*(lower5) + (34105024060867/2500000000000 : ℝ)*(major0) + (34105024060867/2500000000000 : ℝ)*(major1) + (34105024060867/2500000000000 : ℝ)*(major2) + (491715278918729/25000000000000 : ℝ)*(sp0) + (983427185156409/50000000000000 : ℝ)*(sp1) + (1966857840453269/100000000000000 : ℝ)*(sp2) + (37116331661641/5000000000000 : ℝ)*(sp3) + (8566253151/50000000000000 : ℝ)*(sp5) + (13662365851/100000000000000 : ℝ)*(sp6) + (953113247/20000000000000 : ℝ)*(sp7) + (2077428841/20000000000000 : ℝ)*(sp8) + (148466279759811/20000000000000 : ℝ)*(f.failure) + (24585893785239/1250000000000 : ℝ)*(f.sum) + (4184206806401/1913000000000000000000000000 : ℝ)*base66 + (18517246063341999/95650000000000000000000000000000 : ℝ)*base68 + (214454752519908001/95650000000000000000000000000000 : ℝ)*base69 + (744509124042808001/95650000000000000000000000000000 : ℝ)*base71 + (1535346278451/478250000000000000000000000 : ℝ)*base74 + (969654113542758001/95650000000000000000000000000000 : ℝ)*base75 + (324672544608808001/95650000000000000000000000000000 : ℝ)*base77 + (669150375971858001/95650000000000000000000000000000 : ℝ)*base79 + (8500182242869/1913000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (12762311/2000000000000000000000 : ℝ)*base90 + (12762311/2000000000000000000000 : ℝ)*base92 + (12762311/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10037/12500 : ℝ) ≤ (1228887459328775625064519881/1530400000000000000000000000 : ℝ) := by norm_num
    linear_combination (25133781/50000000000000 : ℝ)*(upper0) + (18077611/100000000000000 : ℝ)*(lower1) + (6676647/6250000000000 : ℝ)*(lower3) + (24185291/25000000000000 : ℝ)*(upper4) + (280436636595921/20000000000000 : ℝ)*(major0) + (280436636595921/20000000000000 : ℝ)*(major1) + (280436636595921/20000000000000 : ℝ)*(major2) + (7870362571/100000000000000 : ℝ)*(sp1) + (241360019/10000000000000 : ℝ)*(sp2) + (2783848671/25000000000000 : ℝ)*(sp3) + (1007300376020191/50000000000000 : ℝ)*(sp8) + (2014592881677811/100000000000000 : ℝ)*(sp9) + (1967381189883/97656250000 : ℝ)*(sp10) + (9537354111853/1250000000000 : ℝ)*(sp11) + (190749866085731/25000000000000 : ℝ)*(f.failure) + (1007300376020191/50000000000000 : ℝ)*(f.sum) + (39627021497561/7652000000000000000000000000 : ℝ)*base66 + (633918449292602037/765200000000000000000000000000000 : ℝ)*base68 + (277977297402597963/765200000000000000000000000000000 : ℝ)*base69 + (7075222586602602037/765200000000000000000000000000000 : ℝ)*base72 + (1621237110851/1530400000000000000000000000 : ℝ)*base73 + (872506224563402037/765200000000000000000000000000000 : ℝ)*base76 + (474359526242597963/765200000000000000000000000000000 : ℝ)*base77 + (1460711090843397963/765200000000000000000000000000000 : ℝ)*base79 + (31135431110377/7652000000000000000000000000 : ℝ)*base82 + (9111769/2500000000000000000000 : ℝ)*base89 + (9111769/2500000000000000000000 : ℝ)*base91 + (9111769/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-562/625 : ℝ) ≤ (-860061023393590337724012598807749/956500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102291277/100000000000000 : ℝ)*(lower0) + (122055793/100000000000000 : ℝ)*(upper1) + (24665633/100000000000000 : ℝ)*(lower2) + (56190103/100000000000000 : ℝ)*(upper5) + (723911125568539/50000000000000 : ℝ)*(major0) + (723911125568539/50000000000000 : ℝ)*(major1) + (723911125568539/50000000000000 : ℝ)*(major2) + (2687991853/100000000000000 : ℝ)*(sp4) + (21804911357/100000000000000 : ℝ)*(sp5) + (10786314517/100000000000000 : ℝ)*(sp7) + (26722253842401/1250000000000 : ℝ)*(sp12) + (16701259300567/781250000000 : ℝ)*(sp13) + (2137782995383933/100000000000000 : ℝ)*(sp14) + (393911612655749/50000000000000 : ℝ)*(sp15) + (157566802325203/20000000000000 : ℝ)*(f.failure) + (2137782995383933/100000000000000 : ℝ)*(f.sum) + (51508661869351/19130000000000000000000000000 : ℝ)*base66 + (628381547098052583/1913000000000000000000000000000000 : ℝ)*base68 + (1786792706373947417/1913000000000000000000000000000000 : ℝ)*base69 + (341053641600052583/1913000000000000000000000000000000 : ℝ)*base72 + (24354510522311/19130000000000000000000000000 : ℝ)*base74 + (2084728592862947417/1913000000000000000000000000000000 : ℝ)*base75 + (4488054919168052583/1913000000000000000000000000000000 : ℝ)*base78 + (1445767439115052583/1913000000000000000000000000000000 : ℝ)*base80 + (18390878425149/19130000000000000000000000000 : ℝ)*base81 + (5992297/2000000000000000000000 : ℝ)*base89 + (5992297/2000000000000000000000 : ℝ)*base91 + (5992297/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1676_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17333/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9681/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16617/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11519/20000 : ℝ) else (10037/12500 : ℝ) ≤ X j i ∧ X j i ≤ (562/625 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1676_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1676_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16617/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11519/20000 : ℝ) else (10037/12500 : ℝ) ≤ X j i ∧ X j i ≤ (562/625 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1676_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1676_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1676_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5023/1024 : ℝ) ≤ p) (hpb : p ≤ (5031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183772499/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (603/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16617/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11519/20000 : ℝ) else (10037/12500 : ℝ) ≤ X j i ∧ X j i ≤ (562/625 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1676_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
