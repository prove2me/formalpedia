-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1674_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:19.542179+00:00
-- url     : https://prove2.me/submissions/1a1fe189-86cf-4687-b29d-329b8cfcf737

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
theorem support_rectangle_w1674_s3_0 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1555511141/10000000000 : ℝ)*x 0 + (5440572989/10000000000 : ℝ)*x 1 + (2592612359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1555511141/10000000000 : ℝ)^5015 ≤ (4824986691709/50000000000000 : ℝ)^3991 := by
    have hnat : (1555511141 : ℕ)^5015*50000000000000^3991 ≤ 4824986691709^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555511141 10000000000 4824986691709 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440572989/10000000000 : ℝ)^5015 ≤ (23269500528353/50000000000000 : ℝ)^3991 := by
    have hnat : (5440572989 : ℕ)^5015*50000000000000^3991 ≤ 23269500528353^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440572989 10000000000 23269500528353 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592612359/5000000000 : ℝ)^5015 ≤ (43811025546321/100000000000000 : ℝ)^3991 := by
    have hnat : (2592612359 : ℕ)^5015*100000000000000^3991 ≤ 43811025546321^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592612359 5000000000 43811025546321 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1555511141/10000000000 : ℝ), (5440572989/10000000000 : ℝ), (2592612359/5000000000 : ℝ)] ![(4824986691709/50000000000000 : ℝ), (23269500528353/50000000000000 : ℝ), (43811025546321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1555511141/10000000000 : ℝ)|^5015 ≤ (4824986691709/50000000000000 : ℝ)^3991
        have hw : |(-1555511141/10000000000 : ℝ)|=(1555511141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440572989/10000000000 : ℝ)|^5015 ≤ (23269500528353/50000000000000 : ℝ)^3991
        have hw : |(5440572989/10000000000 : ℝ)|=(5440572989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592612359/5000000000 : ℝ)|^5015 ≤ (43811025546321/100000000000000 : ℝ)^3991
        have hw : |(2592612359/5000000000 : ℝ)|=(2592612359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s3_1 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334005991/625000000 : ℝ)*x 0 + (-421710401/2500000000 : ℝ)*x 1 + (2592612371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334005991/625000000 : ℝ)^5015 ≤ (22752176657293/50000000000000 : ℝ)^3991 := by
    have hnat : (334005991 : ℕ)^5015*50000000000000^3991 ≤ 22752176657293^3991*625000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334005991 625000000 22752176657293 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421710401/2500000000 : ℝ)^5015 ≤ (667788804477/6250000000000 : ℝ)^3991 := by
    have hnat : (421710401 : ℕ)^5015*6250000000000^3991 ≤ 667788804477^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421710401 2500000000 667788804477 6250000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592612371/5000000000 : ℝ)^5015 ≤ (43811025801131/100000000000000 : ℝ)^3991 := by
    have hnat : (2592612371 : ℕ)^5015*100000000000000^3991 ≤ 43811025801131^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592612371 5000000000 43811025801131 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334005991/625000000 : ℝ), (-421710401/2500000000 : ℝ), (2592612371/5000000000 : ℝ)] ![(22752176657293/50000000000000 : ℝ), (667788804477/6250000000000 : ℝ), (43811025801131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334005991/625000000 : ℝ)|^5015 ≤ (22752176657293/50000000000000 : ℝ)^3991
        have hw : |(334005991/625000000 : ℝ)|=(334005991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421710401/2500000000 : ℝ)|^5015 ≤ (667788804477/6250000000000 : ℝ)^3991
        have hw : |(-421710401/2500000000 : ℝ)|=(421710401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592612371/5000000000 : ℝ)|^5015 ≤ (43811025801131/100000000000000 : ℝ)^3991
        have hw : |(2592612371/5000000000 : ℝ)|=(2592612371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s3_2 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068819161/2000000000 : ℝ)*x 0 + (5185224727/10000000000 : ℝ)*x 1 + (-1686841691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068819161/2000000000 : ℝ)^5015 ≤ (22752176384453/50000000000000 : ℝ)^3991 := by
    have hnat : (1068819161 : ℕ)^5015*50000000000000^3991 ≤ 22752176384453^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068819161 2000000000 22752176384453 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185224727/10000000000 : ℝ)^5015 ≤ (70097641027/160000000000 : ℝ)^3991 := by
    have hnat : (5185224727 : ℕ)^5015*160000000000^3991 ≤ 70097641027^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185224727 10000000000 70097641027 160000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1686841691/10000000000 : ℝ)^5015 ≤ (1068462156409/10000000000000 : ℝ)^3991 := by
    have hnat : (1686841691 : ℕ)^5015*10000000000000^3991 ≤ 1068462156409^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686841691 10000000000 1068462156409 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068819161/2000000000 : ℝ), (5185224727/10000000000 : ℝ), (-1686841691/10000000000 : ℝ)] ![(22752176384453/50000000000000 : ℝ), (70097641027/160000000000 : ℝ), (1068462156409/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068819161/2000000000 : ℝ)|^5015 ≤ (22752176384453/50000000000000 : ℝ)^3991
        have hw : |(1068819161/2000000000 : ℝ)|=(1068819161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185224727/10000000000 : ℝ)|^5015 ≤ (70097641027/160000000000 : ℝ)^3991
        have hw : |(5185224727/10000000000 : ℝ)|=(5185224727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1686841691/10000000000 : ℝ)|^5015 ≤ (1068462156409/10000000000000 : ℝ)^3991
        have hw : |(-1686841691/10000000000 : ℝ)|=(1686841691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s3_3 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2081354359/5000000000 : ℝ)*x 0 + (383212267/1000000000 : ℝ)*x 1 + (564098471/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081354359/5000000000 : ℝ)^5015 ≤ (1662212541871/5000000000000 : ℝ)^3991 := by
    have hnat : (2081354359 : ℕ)^5015*5000000000000^3991 ≤ 1662212541871^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081354359 5000000000 1662212541871 5000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383212267/1000000000 : ℝ)^5015 ≤ (14980607116387/50000000000000 : ℝ)^3991 := by
    have hnat : (383212267 : ℕ)^5015*50000000000000^3991 ≤ 14980607116387^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383212267 1000000000 14980607116387 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564098471/1250000000 : ℝ)^5015 ≤ (18397267458769/50000000000000 : ℝ)^3991 := by
    have hnat : (564098471 : ℕ)^5015*50000000000000^3991 ≤ 18397267458769^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564098471 1250000000 18397267458769 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081354359/5000000000 : ℝ), (383212267/1000000000 : ℝ), (564098471/1250000000 : ℝ)] ![(1662212541871/5000000000000 : ℝ), (14980607116387/50000000000000 : ℝ), (18397267458769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081354359/5000000000 : ℝ)|^5015 ≤ (1662212541871/5000000000000 : ℝ)^3991
        have hw : |(2081354359/5000000000 : ℝ)|=(2081354359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(383212267/1000000000 : ℝ)|^5015 ≤ (14980607116387/50000000000000 : ℝ)^3991
        have hw : |(383212267/1000000000 : ℝ)|=(383212267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564098471/1250000000 : ℝ)|^5015 ≤ (18397267458769/50000000000000 : ℝ)^3991
        have hw : |(564098471/1250000000 : ℝ)|=(564098471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s3_4 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-77778613/500000000 : ℝ)*x 0 + (5187177447/10000000000 : ℝ)*x 1 + (1087719937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77778613/500000000 : ℝ)^5015 ≤ (1930089967407/20000000000000 : ℝ)^3991 := by
    have hnat : (77778613 : ℕ)^5015*20000000000000^3991 ≤ 1930089967407^3991*500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77778613 500000000 1930089967407 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187177447/10000000000 : ℝ)^5015 ≤ (43831758825801/100000000000000 : ℝ)^3991 := by
    have hnat : (5187177447 : ℕ)^5015*100000000000000^3991 ≤ 43831758825801^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187177447 10000000000 43831758825801 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087719937/2000000000 : ℝ)^5015 ≤ (290736195709/625000000000 : ℝ)^3991 := by
    have hnat : (1087719937 : ℕ)^5015*625000000000^3991 ≤ 290736195709^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087719937 2000000000 290736195709 625000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77778613/500000000 : ℝ), (5187177447/10000000000 : ℝ), (1087719937/2000000000 : ℝ)] ![(1930089967407/20000000000000 : ℝ), (43831758825801/100000000000000 : ℝ), (290736195709/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77778613/500000000 : ℝ)|^5015 ≤ (1930089967407/20000000000000 : ℝ)^3991
        have hw : |(-77778613/500000000 : ℝ)|=(77778613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187177447/10000000000 : ℝ)|^5015 ≤ (43831758825801/100000000000000 : ℝ)^3991
        have hw : |(5187177447/10000000000 : ℝ)|=(5187177447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087719937/2000000000 : ℝ)|^5015 ≤ (290736195709/625000000000 : ℝ)^3991
        have hw : |(1087719937/2000000000 : ℝ)|=(1087719937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s3_5 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275710331/10000000000 : ℝ)*x 0 + (-1433466653/10000000000 : ℝ)*x 1 + (1087719941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275710331/10000000000 : ℝ)^5015 ≤ (44773859936191/100000000000000 : ℝ)^3991 := by
    have hnat : (5275710331 : ℕ)^5015*100000000000000^3991 ≤ 44773859936191^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275710331 10000000000 44773859936191 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1433466653/10000000000 : ℝ)^5015 ≤ (8708348523347/100000000000000 : ℝ)^3991 := by
    have hnat : (1433466653 : ℕ)^5015*100000000000000^3991 ≤ 8708348523347^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1433466653 10000000000 8708348523347 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087719941/2000000000 : ℝ)^5015 ≤ (11629447882099/25000000000000 : ℝ)^3991 := by
    have hnat : (1087719941 : ℕ)^5015*25000000000000^3991 ≤ 11629447882099^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087719941 2000000000 11629447882099 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275710331/10000000000 : ℝ), (-1433466653/10000000000 : ℝ), (1087719941/2000000000 : ℝ)] ![(44773859936191/100000000000000 : ℝ), (8708348523347/100000000000000 : ℝ), (11629447882099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275710331/10000000000 : ℝ)|^5015 ≤ (44773859936191/100000000000000 : ℝ)^3991
        have hw : |(5275710331/10000000000 : ℝ)|=(5275710331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1433466653/10000000000 : ℝ)|^5015 ≤ (8708348523347/100000000000000 : ℝ)^3991
        have hw : |(-1433466653/10000000000 : ℝ)|=(1433466653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087719941/2000000000 : ℝ)|^5015 ≤ (11629447882099/25000000000000 : ℝ)^3991
        have hw : |(1087719941/2000000000 : ℝ)|=(1087719941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s3_6 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318927589/2500000000 : ℝ)*x 0 + (1359649927/2500000000 : ℝ)*x 1 + (-716733307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318927589/2500000000 : ℝ)^5015 ≤ (44773860202799/100000000000000 : ℝ)^3991 := by
    have hnat : (1318927589 : ℕ)^5015*100000000000000^3991 ≤ 44773860202799^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318927589 2500000000 44773860202799 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359649927/2500000000 : ℝ)^5015 ≤ (145368098627/312500000000 : ℝ)^3991 := by
    have hnat : (1359649927 : ℕ)^5015*312500000000^3991 ≤ 145368098627^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359649927 2500000000 145368098627 312500000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (716733307/5000000000 : ℝ)^5015 ≤ (8708348225631/100000000000000 : ℝ)^3991 := by
    have hnat : (716733307 : ℕ)^5015*100000000000000^3991 ≤ 8708348225631^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716733307 5000000000 8708348225631 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318927589/2500000000 : ℝ), (1359649927/2500000000 : ℝ), (-716733307/5000000000 : ℝ)] ![(44773860202799/100000000000000 : ℝ), (145368098627/312500000000 : ℝ), (8708348225631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318927589/2500000000 : ℝ)|^5015 ≤ (44773860202799/100000000000000 : ℝ)^3991
        have hw : |(1318927589/2500000000 : ℝ)|=(1318927589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359649927/2500000000 : ℝ)|^5015 ≤ (145368098627/312500000000 : ℝ)^3991
        have hw : |(1359649927/2500000000 : ℝ)|=(1359649927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-716733307/5000000000 : ℝ)|^5015 ≤ (8708348225631/100000000000000 : ℝ)^3991
        have hw : |(-716733307/5000000000 : ℝ)|=(716733307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s3_7 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2081435833/5000000000 : ℝ)*x 0 + (450758257/1000000000 : ℝ)*x 1 + (959345673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081435833/5000000000 : ℝ)^5015 ≤ (33245886075353/100000000000000 : ℝ)^3991 := by
    have hnat : (2081435833 : ℕ)^5015*100000000000000^3991 ≤ 33245886075353^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081435833 5000000000 33245886075353 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450758257/1000000000 : ℝ)^5015 ≤ (7348242727039/20000000000000 : ℝ)^3991 := by
    have hnat : (450758257 : ℕ)^5015*20000000000000^3991 ≤ 7348242727039^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450758257 1000000000 7348242727039 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959345673/2500000000 : ℝ)^5015 ≤ (30012900268067/100000000000000 : ℝ)^3991 := by
    have hnat : (959345673 : ℕ)^5015*100000000000000^3991 ≤ 30012900268067^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959345673 2500000000 30012900268067 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081435833/5000000000 : ℝ), (450758257/1000000000 : ℝ), (959345673/2500000000 : ℝ)] ![(33245886075353/100000000000000 : ℝ), (7348242727039/20000000000000 : ℝ), (30012900268067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081435833/5000000000 : ℝ)|^5015 ≤ (33245886075353/100000000000000 : ℝ)^3991
        have hw : |(2081435833/5000000000 : ℝ)|=(2081435833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450758257/1000000000 : ℝ)|^5015 ≤ (7348242727039/20000000000000 : ℝ)^3991
        have hw : |(450758257/1000000000 : ℝ)|=(450758257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(959345673/2500000000 : ℝ)|^5015 ≤ (30012900268067/100000000000000 : ℝ)^3991
        have hw : |(959345673/2500000000 : ℝ)|=(959345673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1674_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2157/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8111/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10741/100000 : ℝ) ^ (5011/1024 : ℝ) ≤ (362572053691999/20000000000000000000 : ℝ) := by
    have hpowers : (10741/100000 : ℝ)^5011 ≤ (362572053691999/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10741 : ℕ)^5011*20000000000000000000^1024 ≤ 362572053691999^1024*100000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10741 100000 362572053691999 20000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10741/100000 : ℝ)) (X := (362572053691999/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16271/100000 : ℝ) ^ (5011/1024 : ℝ) ≤ (13836061460514693/100000000000000000000 : ℝ) := by
    have hpowers : (16271/100000 : ℝ)^5011 ≤ (13836061460514693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16271 : ℕ)^5011*100000000000000000000^1024 ≤ 13836061460514693^1024*100000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16271 100000 13836061460514693 100000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16271/100000 : ℝ)) (X := (13836061460514693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000362572053691999/10000000000000000000 : ℝ) ≤ (10000074090686059/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (10000362572053691999/10000000000000000000 : ℝ)^1024 ≤ (10000074090686059/10000000000000000 : ℝ)^5011 := by
      have hnat : (10000362572053691999 : ℕ)^1024*10000000000000000^5011 ≤ 10000074090686059^5011*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000362572053691999 10000000000000000000 10000074090686059 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000074090686059/10000000000000000 : ℝ)) (X := (10000362572053691999/10000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125489028804030459/3125000000000000000 : ℝ) ≤ (10000319766480429/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (3125489028804030459/3125000000000000000 : ℝ)^1024 ≤ (10000319766480429/10000000000000000 : ℝ)^5011 := by
      have hnat : (3125489028804030459 : ℕ)^1024*10000000000000000^5011 ≤ 10000319766480429^5011*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125489028804030459 3125000000000000000 10000319766480429 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000319766480429/10000000000000000 : ℝ)) (X := (3125489028804030459/3125000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013836061460514693/50000000000000000000 : ℝ) ≤ (10000565442274799/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (50013836061460514693/50000000000000000000 : ℝ)^1024 ≤ (10000565442274799/10000000000000000 : ℝ)^5011 := by
      have hnat : (50013836061460514693 : ℕ)^1024*10000000000000000^5011 ≤ 10000565442274799^5011*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013836061460514693 50000000000000000000 10000565442274799 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000565442274799/10000000000000000 : ℝ)) (X := (50013836061460514693/50000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(362572053691999/20000000000000000000 : ℝ) ≤ ((5529513211407924993/5530000000000000000 : ℝ)+2*(24567579437/55300000000000 : ℝ)*(10741/100000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (5529513211407924993/5530000000000000000 : ℝ)+2*(24567579437/55300000000000 : ℝ)*(10741/100000 : ℝ)=(10000074090686059/10000000000000000 : ℝ) by norm_num, show 1+2*(362572053691999/20000000000000000000 : ℝ)=(10000362572053691999/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13836061460514693/100000000000000000000 : ℝ)+(362572053691999/20000000000000000000 : ℝ) ≤ ((5529513211407924993/5530000000000000000 : ℝ)+(24567579437/55300000000000 : ℝ)*((16271/100000 : ℝ)+(10741/100000 : ℝ)))^(5011/1024 : ℝ) := by
    rw [show (5529513211407924993/5530000000000000000 : ℝ)+(24567579437/55300000000000 : ℝ)*((16271/100000 : ℝ)+(10741/100000 : ℝ))=(10000319766480429/10000000000000000 : ℝ) by norm_num, show 1+(13836061460514693/100000000000000000000 : ℝ)+(362572053691999/20000000000000000000 : ℝ)=(3125489028804030459/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13836061460514693/100000000000000000000 : ℝ) ≤ ((5529513211407924993/5530000000000000000 : ℝ)+2*(24567579437/55300000000000 : ℝ)*(16271/100000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (5529513211407924993/5530000000000000000 : ℝ)+2*(24567579437/55300000000000 : ℝ)*(16271/100000 : ℝ)=(10000565442274799/10000000000000000 : ℝ) by norm_num, show 1+2*(13836061460514693/100000000000000000000 : ℝ)=(50013836061460514693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5529513211407924993/5530000000000000000 : ℝ)*(X 1 0+X 2 0)+(24567579437/55300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10741/100000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (5529513211407924993/5530000000000000000 : ℝ)) (alpha := (24567579437/55300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5529513211407924993/5530000000000000000 : ℝ)*(X 0 1+X 2 1)+(24567579437/55300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10741/100000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (5529513211407924993/5530000000000000000 : ℝ)) (alpha := (24567579437/55300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5529513211407924993/5530000000000000000 : ℝ)*(X 0 2+X 1 2)+(24567579437/55300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10741/100000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (5529513211407924993/5530000000000000000 : ℝ)) (alpha := (24567579437/55300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1555511141/10000000000 : ℝ)*X 0 0+(5440572989/10000000000 : ℝ)*X 0 1+(2592612359/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334005991/625000000 : ℝ)*X 1 0+(-421710401/2500000000 : ℝ)*X 1 1+(2592612371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068819161/2000000000 : ℝ)*X 2 0+(5185224727/10000000000 : ℝ)*X 2 1+(-1686841691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2081354359/5000000000 : ℝ)*X 0 0+(383212267/1000000000 : ℝ)*X 0 1+(564098471/1250000000 : ℝ)*X 0 2+(2081354359/5000000000 : ℝ)*X 1 0+(383212267/1000000000 : ℝ)*X 1 1+(564098471/1250000000 : ℝ)*X 1 2+(2081354359/5000000000 : ℝ)*X 2 0+(383212267/1000000000 : ℝ)*X 2 1+(564098471/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-77778613/500000000 : ℝ)*X 0 0+(5187177447/10000000000 : ℝ)*X 0 1+(1087719937/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275710331/10000000000 : ℝ)*X 1 0+(-1433466653/10000000000 : ℝ)*X 1 1+(1087719941/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1318927589/2500000000 : ℝ)*X 2 0+(1359649927/2500000000 : ℝ)*X 2 1+(-716733307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2081435833/5000000000 : ℝ)*X 0 0+(450758257/1000000000 : ℝ)*X 0 1+(959345673/2500000000 : ℝ)*X 0 2+(2081435833/5000000000 : ℝ)*X 1 0+(450758257/1000000000 : ℝ)*X 1 1+(959345673/2500000000 : ℝ)*X 1 2+(2081435833/5000000000 : ℝ)*X 2 0+(450758257/1000000000 : ℝ)*X 2 1+(959345673/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (818350442622175910730068277/138250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181166853/20000000000000 : ℝ)*(base19) + (799058371/100000000000000 : ℝ)*(base23) + (18544613/50000000000000 : ℝ)*(lower2) + (184336217/100000000000000 : ℝ)*(upper3) + (11694719/20000000000000 : ℝ)*(upper5) + (2692701687557463/100000000000000 : ℝ)*(major0) + (2692701687557463/100000000000000 : ℝ)*(major1) + (2692701687557463/100000000000000 : ℝ)*(major2) + (1958116406565059/50000000000000 : ℝ)*(sp0) + (1958121108095733/50000000000000 : ℝ)*(sp1) + (12238257259273/312500000000 : ℝ)*(sp2) + (11477774122999/781250000000 : ℝ)*(sp3) + (10308895613/100000000000000 : ℝ)*(sp4) + (4968033577/100000000000000 : ℝ)*(sp7) + (1469160055777449/100000000000000 : ℝ)*(f.failure) + (3916243122025731/100000000000000 : ℝ)*(f.sum) + (9568695967931/2765000000000000000000000000 : ℝ)*base65 + (3611096447064527241/553000000000000000000000000000000 : ℝ)*base68 + (5401484693662527241/553000000000000000000000000000000 : ℝ)*base70 + (5421572233407527241/553000000000000000000000000000000 : ℝ)*base72 + (3484632088159/2765000000000000000000000000 : ℝ)*base74 + (2258166338258472759/553000000000000000000000000000000 : ℝ)*base75 + (2200214460319527241/553000000000000000000000000000000 : ℝ)*base78 + (5448100514935527241/553000000000000000000000000000000 : ℝ)*base80 + (7982793684969/2765000000000000000000000000 : ℝ)*base82 + (12064761/10000000000000000000000 : ℝ)*base90 + (12064761/10000000000000000000000 : ℝ)*base92 + (12064761/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22185546714779102655723831/2468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1290667441/100000000000000 : ℝ)*(base19) + (1449392479/100000000000000 : ℝ)*(base23) + (98770571/50000000000000 : ℝ)*(upper3) + (28560053/50000000000000 : ℝ)*(lower4) + (88114463/50000000000000 : ℝ)*(upper5) + (170920751564973/6250000000000 : ℝ)*(major0) + (170920751564973/6250000000000 : ℝ)*(major1) + (170920751564973/6250000000000 : ℝ)*(major2) + (1969110731/12500000000000 : ℝ)*(sp1) + (18191316961/100000000000000 : ℝ)*(sp2) + (994342899746813/25000000000000 : ℝ)*(sp4) + (1988677277716981/50000000000000 : ℝ)*(sp5) + (397735195827781/10000000000000 : ℝ)*(sp6) + (373023037885047/25000000000000 : ℝ)*(sp7) + (373023037885047/25000000000000 : ℝ)*(f.failure) + (994342899746813/25000000000000 : ℝ)*(f.sum) + (898835279263/345625000000000000000000000 : ℝ)*base66 + (541829445168079811/34562500000000000000000000000000 : ℝ)*base68 + (349309853939079811/34562500000000000000000000000000 : ℝ)*base70 + (306285721283204811/34562500000000000000000000000000 : ℝ)*base72 + (4373343122007/1382500000000000000000000000 : ℝ)*base74 + (211113590203545189/34562500000000000000000000000000 : ℝ)*base75 + (133402079734142311/34562500000000000000000000000000 : ℝ)*base78 + (256368387888232689/34562500000000000000000000000000 : ℝ)*base79 + (5561229071109/2765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (35475417/2500000000000000000000 : ℝ)*base89 + (35475417/2500000000000000000000 : ℝ)*base91 + (35475417/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1674_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8111/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1674_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1674_s4_0 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1555536737/10000000000 : ℝ)*x 0 + (340027679/625000000 : ℝ)*x 1 + (5185337663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1555536737/10000000000 : ℝ)^5015 ≤ (9650172916641/100000000000000 : ℝ)^3991 := by
    have hnat : (1555536737 : ℕ)^5015*100000000000000^3991 ≤ 9650172916641^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555536737 10000000000 9650172916641 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340027679/625000000 : ℝ)^5015 ≤ (9307520473621/20000000000000 : ℝ)^3991 := by
    have hnat : (340027679 : ℕ)^5015*20000000000000^3991 ≤ 9307520473621^3991*625000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340027679 625000000 9307520473621 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185337663/10000000000 : ℝ)^5015 ≤ (10953056173913/25000000000000 : ℝ)^3991 := by
    have hnat : (5185337663 : ℕ)^5015*25000000000000^3991 ≤ 10953056173913^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185337663 10000000000 10953056173913 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1555536737/10000000000 : ℝ), (340027679/625000000 : ℝ), (5185337663/10000000000 : ℝ)] ![(9650172916641/100000000000000 : ℝ), (9307520473621/20000000000000 : ℝ), (10953056173913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1555536737/10000000000 : ℝ)|^5015 ≤ (9650172916641/100000000000000 : ℝ)^3991
        have hw : |(-1555536737/10000000000 : ℝ)|=(1555536737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340027679/625000000 : ℝ)|^5015 ≤ (9307520473621/20000000000000 : ℝ)^3991
        have hw : |(340027679/625000000 : ℝ)|=(340027679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185337663/10000000000 : ℝ)|^5015 ≤ (10953056173913/25000000000000 : ℝ)^3991
        have hw : |(5185337663/10000000000 : ℝ)|=(5185337663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s4_1 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668007497/1250000000 : ℝ)*x 0 + (-1686738801/10000000000 : ℝ)*x 1 + (324083623/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668007497/1250000000 : ℝ)^5015 ≤ (45503969412937/100000000000000 : ℝ)^3991 := by
    have hnat : (668007497 : ℕ)^5015*100000000000000^3991 ≤ 45503969412937^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668007497 1250000000 45503969412937 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1686738801/10000000000 : ℝ)^5015 ≤ (10683802639717/100000000000000 : ℝ)^3991 := by
    have hnat : (1686738801 : ℕ)^5015*100000000000000^3991 ≤ 10683802639717^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686738801 10000000000 10683802639717 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324083623/625000000 : ℝ)^5015 ≤ (1095305698347/2500000000000 : ℝ)^3991 := by
    have hnat : (324083623 : ℕ)^5015*2500000000000^3991 ≤ 1095305698347^3991*625000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324083623 625000000 1095305698347 2500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668007497/1250000000 : ℝ), (-1686738801/10000000000 : ℝ), (324083623/625000000 : ℝ)] ![(45503969412937/100000000000000 : ℝ), (10683802639717/100000000000000 : ℝ), (1095305698347/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668007497/1250000000 : ℝ)|^5015 ≤ (45503969412937/100000000000000 : ℝ)^3991
        have hw : |(668007497/1250000000 : ℝ)|=(668007497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1686738801/10000000000 : ℝ)|^5015 ≤ (10683802639717/100000000000000 : ℝ)^3991
        have hw : |(-1686738801/10000000000 : ℝ)|=(1686738801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324083623/625000000 : ℝ)|^5015 ≤ (1095305698347/2500000000000 : ℝ)^3991
        have hw : |(324083623/625000000 : ℝ)|=(324083623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s4_2 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344060037/10000000000 : ℝ)*x 0 + (5185338071/10000000000 : ℝ)*x 1 + (-843369291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344060037/10000000000 : ℝ)^5015 ≤ (11375992516403/25000000000000 : ℝ)^3991 := by
    have hnat : (5344060037 : ℕ)^5015*25000000000000^3991 ≤ 11375992516403^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344060037 10000000000 11375992516403 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185338071/10000000000 : ℝ)^5015 ≤ (8762445805489/20000000000000 : ℝ)^3991 := by
    have hnat : (5185338071 : ℕ)^5015*20000000000000^3991 ≤ 8762445805489^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185338071 10000000000 8762445805489 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (843369291/5000000000 : ℝ)^5015 ≤ (10683800896661/100000000000000 : ℝ)^3991 := by
    have hnat : (843369291 : ℕ)^5015*100000000000000^3991 ≤ 10683800896661^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843369291 5000000000 10683800896661 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344060037/10000000000 : ℝ), (5185338071/10000000000 : ℝ), (-843369291/5000000000 : ℝ)] ![(11375992516403/25000000000000 : ℝ), (8762445805489/20000000000000 : ℝ), (10683800896661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344060037/10000000000 : ℝ)|^5015 ≤ (11375992516403/25000000000000 : ℝ)^3991
        have hw : |(5344060037/10000000000 : ℝ)|=(5344060037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185338071/10000000000 : ℝ)|^5015 ≤ (8762445805489/20000000000000 : ℝ)^3991
        have hw : |(5185338071/10000000000 : ℝ)|=(5185338071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-843369291/5000000000 : ℝ)|^5015 ≤ (10683800896661/100000000000000 : ℝ)^3991
        have hw : |(-843369291/5000000000 : ℝ)|=(843369291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s4_3 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65042589/156250000 : ℝ)*x 0 + (479055677/1250000000 : ℝ)*x 1 + (902492329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65042589/156250000 : ℝ)^5015 ≤ (33244421216589/100000000000000 : ℝ)^3991 := by
    have hnat : (65042589 : ℕ)^5015*100000000000000^3991 ≤ 33244421216589^3991*156250000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65042589 156250000 33244421216589 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479055677/1250000000 : ℝ)^5015 ≤ (5992877015211/20000000000000 : ℝ)^3991 := by
    have hnat : (479055677 : ℕ)^5015*20000000000000^3991 ≤ 5992877015211^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479055677 1250000000 5992877015211 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902492329/2000000000 : ℝ)^5015 ≤ (1839559684897/5000000000000 : ℝ)^3991 := by
    have hnat : (902492329 : ℕ)^5015*5000000000000^3991 ≤ 1839559684897^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902492329 2000000000 1839559684897 5000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65042589/156250000 : ℝ), (479055677/1250000000 : ℝ), (902492329/2000000000 : ℝ)] ![(33244421216589/100000000000000 : ℝ), (5992877015211/20000000000000 : ℝ), (1839559684897/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65042589/156250000 : ℝ)|^5015 ≤ (33244421216589/100000000000000 : ℝ)^3991
        have hw : |(65042589/156250000 : ℝ)|=(65042589/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(479055677/1250000000 : ℝ)|^5015 ≤ (5992877015211/20000000000000 : ℝ)^3991
        have hw : |(479055677/1250000000 : ℝ)|=(479055677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902492329/2000000000 : ℝ)|^5015 ≤ (1839559684897/5000000000000 : ℝ)^3991
        have hw : |(902492329/2000000000 : ℝ)|=(902492329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s4_4 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1555597633/10000000000 : ℝ)*x 0 + (1037457361/2000000000 : ℝ)*x 1 + (1359618311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1555597633/10000000000 : ℝ)^5015 ≤ (1930129526771/20000000000000 : ℝ)^3991 := by
    have hnat : (1555597633 : ℕ)^5015*20000000000000^3991 ≤ 1930129526771^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555597633 10000000000 1930129526771 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037457361/2000000000 : ℝ)^5015 ≤ (43832920003633/100000000000000 : ℝ)^3991 := by
    have hnat : (1037457361 : ℕ)^5015*100000000000000^3991 ≤ 43832920003633^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037457361 2000000000 43832920003633 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359618311/2500000000 : ℝ)^5015 ≤ (1860657293993/4000000000000 : ℝ)^3991 := by
    have hnat : (1359618311 : ℕ)^5015*4000000000000^3991 ≤ 1860657293993^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359618311 2500000000 1860657293993 4000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1555597633/10000000000 : ℝ), (1037457361/2000000000 : ℝ), (1359618311/2500000000 : ℝ)] ![(1930129526771/20000000000000 : ℝ), (43832920003633/100000000000000 : ℝ), (1860657293993/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1555597633/10000000000 : ℝ)|^5015 ≤ (1930129526771/20000000000000 : ℝ)^3991
        have hw : |(-1555597633/10000000000 : ℝ)|=(1555597633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037457361/2000000000 : ℝ)|^5015 ≤ (43832920003633/100000000000000 : ℝ)^3991
        have hw : |(1037457361/2000000000 : ℝ)|=(1037457361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359618311/2500000000 : ℝ)|^5015 ≤ (1860657293993/4000000000000 : ℝ)^3991
        have hw : |(1359618311/2500000000 : ℝ)|=(1359618311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s4_5 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275740093/10000000000 : ℝ)*x 0 + (-458753/3200000 : ℝ)*x 1 + (2719236621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275740093/10000000000 : ℝ)^5015 ≤ (44774177327647/100000000000000 : ℝ)^3991 := by
    have hnat : (5275740093 : ℕ)^5015*100000000000000^3991 ≤ 44774177327647^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275740093 10000000000 44774177327647 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458753/3200000 : ℝ)^5015 ≤ (8709390327963/100000000000000 : ℝ)^3991 := by
    have hnat : (458753 : ℕ)^5015*100000000000000^3991 ≤ 8709390327963^3991*3200000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458753 3200000 8709390327963 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719236621/5000000000 : ℝ)^5015 ≤ (46516432328329/100000000000000 : ℝ)^3991 := by
    have hnat : (2719236621 : ℕ)^5015*100000000000000^3991 ≤ 46516432328329^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719236621 5000000000 46516432328329 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275740093/10000000000 : ℝ), (-458753/3200000 : ℝ), (2719236621/5000000000 : ℝ)] ![(44774177327647/100000000000000 : ℝ), (8709390327963/100000000000000 : ℝ), (46516432328329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275740093/10000000000 : ℝ)|^5015 ≤ (44774177327647/100000000000000 : ℝ)^3991
        have hw : |(5275740093/10000000000 : ℝ)|=(5275740093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458753/3200000 : ℝ)|^5015 ≤ (8709390327963/100000000000000 : ℝ)^3991
        have hw : |(-458753/3200000 : ℝ)|=(458753/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719236621/5000000000 : ℝ)|^5015 ≤ (46516432328329/100000000000000 : ℝ)^3991
        have hw : |(2719236621/5000000000 : ℝ)|=(2719236621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s4_6 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275740091/10000000000 : ℝ)*x 0 + (1359618311/2500000000 : ℝ)*x 1 + (-458753/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275740091/10000000000 : ℝ)^5015 ≤ (22387088653159/50000000000000 : ℝ)^3991 := by
    have hnat : (5275740091 : ℕ)^5015*50000000000000^3991 ≤ 22387088653159^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275740091 10000000000 22387088653159 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359618311/2500000000 : ℝ)^5015 ≤ (1860657293993/4000000000000 : ℝ)^3991 := by
    have hnat : (1359618311 : ℕ)^5015*4000000000000^3991 ≤ 1860657293993^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359618311 2500000000 1860657293993 4000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458753/3200000 : ℝ)^5015 ≤ (8709390327963/100000000000000 : ℝ)^3991 := by
    have hnat : (458753 : ℕ)^5015*100000000000000^3991 ≤ 8709390327963^3991*3200000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458753 3200000 8709390327963 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275740091/10000000000 : ℝ), (1359618311/2500000000 : ℝ), (-458753/3200000 : ℝ)] ![(22387088653159/50000000000000 : ℝ), (1860657293993/4000000000000 : ℝ), (8709390327963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275740091/10000000000 : ℝ)|^5015 ≤ (22387088653159/50000000000000 : ℝ)^3991
        have hw : |(5275740091/10000000000 : ℝ)|=(5275740091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359618311/2500000000 : ℝ)|^5015 ≤ (1860657293993/4000000000000 : ℝ)^3991
        have hw : |(1359618311/2500000000 : ℝ)|=(1359618311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458753/3200000 : ℝ)|^5015 ≤ (8709390327963/100000000000000 : ℝ)^3991
        have hw : |(-458753/3200000 : ℝ)|=(458753/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_s4_7 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (416288807/1000000000 : ℝ)*x 0 + (4507266499/10000000000 : ℝ)*x 1 + (1918847667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416288807/1000000000 : ℝ)^5015 ≤ (6649210139183/20000000000000 : ℝ)^3991 := by
    have hnat : (416288807 : ℕ)^5015*20000000000000^3991 ≤ 6649210139183^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416288807 1000000000 6649210139183 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507266499/10000000000 : ℝ)^5015 ≤ (4592247044869/12500000000000 : ℝ)^3991 := by
    have hnat : (4507266499 : ℕ)^5015*12500000000000^3991 ≤ 4592247044869^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507266499 10000000000 4592247044869 12500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918847667/5000000000 : ℝ)^5015 ≤ (30015972923927/100000000000000 : ℝ)^3991 := by
    have hnat : (1918847667 : ℕ)^5015*100000000000000^3991 ≤ 30015972923927^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918847667 5000000000 30015972923927 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416288807/1000000000 : ℝ), (4507266499/10000000000 : ℝ), (1918847667/5000000000 : ℝ)] ![(6649210139183/20000000000000 : ℝ), (4592247044869/12500000000000 : ℝ), (30015972923927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416288807/1000000000 : ℝ)|^5015 ≤ (6649210139183/20000000000000 : ℝ)^3991
        have hw : |(416288807/1000000000 : ℝ)|=(416288807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507266499/10000000000 : ℝ)|^5015 ≤ (4592247044869/12500000000000 : ℝ)^3991
        have hw : |(4507266499/10000000000 : ℝ)|=(4507266499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1918847667/5000000000 : ℝ)|^5015 ≤ (30015972923927/100000000000000 : ℝ)^3991
        have hw : |(1918847667/5000000000 : ℝ)|=(1918847667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1674_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8111/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10787/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16219/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8111/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8111/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8111/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8111/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8111/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8111/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2157/20000 : ℝ) ^ (5011/1024 : ℝ) ≤ (1849492219404121/100000000000000000000 : ℝ) := by
    have hpowers : (2157/20000 : ℝ)^5011 ≤ (1849492219404121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2157 : ℕ)^5011*100000000000000000000^1024 ≤ 1849492219404121^1024*20000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2157 20000 1849492219404121 100000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2157/20000 : ℝ)) (X := (1849492219404121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8111/50000 : ℝ) ^ (5011/1024 : ℝ) ≤ (1363335268123453/10000000000000000000 : ℝ) := by
    have hpowers : (8111/50000 : ℝ)^5011 ≤ (1363335268123453/10000000000000000000 : ℝ)^1024 := by
      have hnat : (8111 : ℕ)^5011*10000000000000000000^1024 ≤ 1363335268123453^1024*50000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8111 50000 1363335268123453 10000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8111/50000 : ℝ)) (X := (1363335268123453/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001849492219404121/50000000000000000000 : ℝ) ≤ (10000075587793413/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (50001849492219404121/50000000000000000000 : ℝ)^1024 ≤ (10000075587793413/10000000000000000 : ℝ)^5011 := by
      have hnat : (50001849492219404121 : ℕ)^1024*10000000000000000^5011 ≤ 10000075587793413^5011*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001849492219404121 50000000000000000000 10000075587793413 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000075587793413/10000000000000000 : ℝ)) (X := (50001849492219404121/50000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015482844900638651/100000000000000000000 : ℝ) ≤ (5000158186556789/5000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (100015482844900638651/100000000000000000000 : ℝ)^1024 ≤ (5000158186556789/5000000000000000 : ℝ)^5011 := by
      have hnat : (100015482844900638651 : ℕ)^1024*5000000000000000^5011 ≤ 5000158186556789^5011*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015482844900638651 100000000000000000000 5000158186556789 5000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000158186556789/5000000000000000 : ℝ)) (X := (100015482844900638651/100000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001363335268123453/5000000000000000000 : ℝ) ≤ (10000557158433743/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (5001363335268123453/5000000000000000000 : ℝ)^1024 ≤ (10000557158433743/10000000000000000 : ℝ)^5011 := by
      have hnat : (5001363335268123453 : ℕ)^1024*10000000000000000^5011 ≤ 10000557158433743^5011*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001363335268123453 5000000000000000000 10000557158433743 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000557158433743/10000000000000000 : ℝ)) (X := (5001363335268123453/5000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1849492219404121/100000000000000000000 : ℝ) ≤ ((54365217231476827431/54370000000000000000 : ℝ)+2*(48157064033/108740000000000 : ℝ)*(2157/20000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (54365217231476827431/54370000000000000000 : ℝ)+2*(48157064033/108740000000000 : ℝ)*(2157/20000 : ℝ)=(10000075587793413/10000000000000000 : ℝ) by norm_num, show 1+2*(1849492219404121/100000000000000000000 : ℝ)=(50001849492219404121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1363335268123453/10000000000000000000 : ℝ)+(1849492219404121/100000000000000000000 : ℝ) ≤ ((54365217231476827431/54370000000000000000 : ℝ)+(48157064033/108740000000000 : ℝ)*((8111/50000 : ℝ)+(2157/20000 : ℝ)))^(5011/1024 : ℝ) := by
    rw [show (54365217231476827431/54370000000000000000 : ℝ)+(48157064033/108740000000000 : ℝ)*((8111/50000 : ℝ)+(2157/20000 : ℝ))=(5000158186556789/5000000000000000 : ℝ) by norm_num, show 1+(1363335268123453/10000000000000000000 : ℝ)+(1849492219404121/100000000000000000000 : ℝ)=(100015482844900638651/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1363335268123453/10000000000000000000 : ℝ) ≤ ((54365217231476827431/54370000000000000000 : ℝ)+2*(48157064033/108740000000000 : ℝ)*(8111/50000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (54365217231476827431/54370000000000000000 : ℝ)+2*(48157064033/108740000000000 : ℝ)*(8111/50000 : ℝ)=(10000557158433743/10000000000000000 : ℝ) by norm_num, show 1+2*(1363335268123453/10000000000000000000 : ℝ)=(5001363335268123453/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54365217231476827431/54370000000000000000 : ℝ)*(X 1 0+X 2 0)+(48157064033/108740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (8111/50000 : ℝ)) (c := (54365217231476827431/54370000000000000000 : ℝ)) (alpha := (48157064033/108740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54365217231476827431/54370000000000000000 : ℝ)*(X 0 1+X 2 1)+(48157064033/108740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (8111/50000 : ℝ)) (c := (54365217231476827431/54370000000000000000 : ℝ)) (alpha := (48157064033/108740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54365217231476827431/54370000000000000000 : ℝ)*(X 0 2+X 1 2)+(48157064033/108740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (8111/50000 : ℝ)) (c := (54365217231476827431/54370000000000000000 : ℝ)) (alpha := (48157064033/108740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1555536737/10000000000 : ℝ)*X 0 0+(340027679/625000000 : ℝ)*X 0 1+(5185337663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668007497/1250000000 : ℝ)*X 1 0+(-1686738801/10000000000 : ℝ)*X 1 1+(324083623/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344060037/10000000000 : ℝ)*X 2 0+(5185338071/10000000000 : ℝ)*X 2 1+(-843369291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((65042589/156250000 : ℝ)*X 0 0+(479055677/1250000000 : ℝ)*X 0 1+(902492329/2000000000 : ℝ)*X 0 2+(65042589/156250000 : ℝ)*X 1 0+(479055677/1250000000 : ℝ)*X 1 1+(902492329/2000000000 : ℝ)*X 1 2+(65042589/156250000 : ℝ)*X 2 0+(479055677/1250000000 : ℝ)*X 2 1+(902492329/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1555597633/10000000000 : ℝ)*X 0 0+(1037457361/2000000000 : ℝ)*X 0 1+(1359618311/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275740093/10000000000 : ℝ)*X 1 0+(-458753/3200000 : ℝ)*X 1 1+(2719236621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275740091/10000000000 : ℝ)*X 2 0+(1359618311/2500000000 : ℝ)*X 2 1+(-458753/3200000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((416288807/1000000000 : ℝ)*X 0 0+(4507266499/10000000000 : ℝ)*X 0 1+(1918847667/5000000000 : ℝ)*X 0 2+(416288807/1000000000 : ℝ)*X 1 0+(4507266499/10000000000 : ℝ)*X 1 1+(1918847667/5000000000 : ℝ)*X 1 2+(416288807/1000000000 : ℝ)*X 2 0+(4507266499/10000000000 : ℝ)*X 2 1+(1918847667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3935141692336746849559018959/339812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174479661/12500000000000 : ℝ)*(base19) + (335232493/25000000000000 : ℝ)*(base23) + (26627377/50000000000000 : ℝ)*(lower2) + (100167649/50000000000000 : ℝ)*(upper3) + (315245937/100000000000000 : ℝ)*(upper5) + (336910088455521/12500000000000 : ℝ)*(major0) + (336910088455521/12500000000000 : ℝ)*(major1) + (336910088455521/12500000000000 : ℝ)*(major2) + (1959985240549093/50000000000000 : ℝ)*(sp0) + (1959996221608799/50000000000000 : ℝ)*(sp1) + (1959996249062457/50000000000000 : ℝ)*(sp2) + (183820049264099/12500000000000 : ℝ)*(sp3) + (233579567/1000000000000 : ℝ)*(sp4) + (679610957/10000000000000 : ℝ)*(sp7) + (735283595111181/50000000000000 : ℝ)*(f.failure) + (1959996919527443/50000000000000 : ℝ)*(f.sum) + (5713611644803/2718500000000000000000000000 : ℝ)*base66 + (7248631862232553449/679625000000000000000000000000000 : ℝ)*base68 + (5847298280655553449/679625000000000000000000000000000 : ℝ)*base70 + (12715362515924803449/679625000000000000000000000000000 : ℝ)*base72 + (56732166211/84953125000000000000000000 : ℝ)*base74 + (1815658625405803449/679625000000000000000000000000000 : ℝ)*base76 + (7421630299961053449/679625000000000000000000000000000 : ℝ)*base78 + (12753195211673803449/679625000000000000000000000000000 : ℝ)*base80 + (15961272271/67962500000000000000000000 : ℝ)*base81 + (88910691/5000000000000000000000 : ℝ)*base89 + (88910691/5000000000000000000000 : ℝ)*base91 + (88910691/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8031554069358776814625616637/1359250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (426425403/50000000000000 : ℝ)*(base19) + (18393981/2000000000000 : ℝ)*(base23) + (52920609/20000000000000 : ℝ)*(lower1) + (30907731/25000000000000 : ℝ)*(upper3) + (15437401/50000000000000 : ℝ)*(lower4) + (122547361/100000000000000 : ℝ)*(upper5) + (2737292463082009/100000000000000 : ℝ)*(major0) + (2737292463082009/100000000000000 : ℝ)*(major1) + (2737292463082009/100000000000000 : ℝ)*(major2) + (379742929/50000000000000 : ℝ)*(sp2) + (398109558173373/10000000000000 : ℝ)*(sp4) + (995273682220731/25000000000000 : ℝ)*(sp5) + (1990546951274411/50000000000000 : ℝ)*(sp6) + (746744573734913/50000000000000 : ℝ)*(sp7) + (746744573734913/50000000000000 : ℝ)*(f.failure) + (398109558173373/10000000000000 : ℝ)*(f.sum) + (15464972504713/5437000000000000000000000000 : ℝ)*base66 + (231769203370245711121/5437000000000000000000000000000000 : ℝ)*base68 + (18330635188905711121/5437000000000000000000000000000000 : ℝ)*base70 + (566361943750781711121/5437000000000000000000000000000000 : ℝ)*base72 + (9057505759241/5437000000000000000000000000 : ℝ)*base74 + (574370873794838288879/5437000000000000000000000000000000 : ℝ)*base75 + (36063102758973711121/5437000000000000000000000000000000 : ℝ)*base78 + (9242502960577711121/5437000000000000000000000000000000 : ℝ)*base80 + (28370426260689/5437000000000000000000000000 : ℝ)*base82 + (65076143/5000000000000000000000 : ℝ)*base89 + (65076143/5000000000000000000000 : ℝ)*base91 + (65076143/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1674_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8111/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16219/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1674_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1674_box_0 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-261171887/2000000000 : ℝ)*x 0 + (2701113339/5000000000 : ℝ)*x 1 + (2701113327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261171887/2000000000 : ℝ)^5015 ≤ (3872804104677/50000000000000 : ℝ)^3991 := by
    have hnat : (261171887 : ℕ)^5015*50000000000000^3991 ≤ 3872804104677^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261171887 2000000000 3872804104677 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701113339/5000000000 : ℝ)^5015 ≤ (1845087840649/4000000000000 : ℝ)^3991 := by
    have hnat : (2701113339 : ℕ)^5015*4000000000000^3991 ≤ 1845087840649^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701113339 5000000000 1845087840649 4000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701113327/5000000000 : ℝ)^5015 ≤ (72073743373/156250000000 : ℝ)^3991 := by
    have hnat : (2701113327 : ℕ)^5015*156250000000^3991 ≤ 72073743373^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701113327 5000000000 72073743373 156250000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261171887/2000000000 : ℝ), (2701113339/5000000000 : ℝ), (2701113327/5000000000 : ℝ)] ![(3872804104677/50000000000000 : ℝ), (1845087840649/4000000000000 : ℝ), (72073743373/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261171887/2000000000 : ℝ)|^5015 ≤ (3872804104677/50000000000000 : ℝ)^3991
        have hw : |(-261171887/2000000000 : ℝ)|=(261171887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701113339/5000000000 : ℝ)|^5015 ≤ (1845087840649/4000000000000 : ℝ)^3991
        have hw : |(2701113339/5000000000 : ℝ)|=(2701113339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701113327/5000000000 : ℝ)|^5015 ≤ (72073743373/156250000000 : ℝ)^3991
        have hw : |(2701113327/5000000000 : ℝ)|=(2701113327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_1 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625292707/5000000000 : ℝ)*x 0 + (-30381303/200000000 : ℝ)*x 1 + (5402226793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625292707/5000000000 : ℝ)^5015 ≤ (44506083900043/100000000000000 : ℝ)^3991 := by
    have hnat : (2625292707 : ℕ)^5015*100000000000000^3991 ≤ 44506083900043^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625292707 5000000000 44506083900043 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30381303/200000000 : ℝ)^5015 ≤ (585419926919/6250000000000 : ℝ)^3991 := by
    have hnat : (30381303 : ℕ)^5015*6250000000000^3991 ≤ 585419926919^3991*200000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30381303 200000000 585419926919 6250000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402226793/10000000000 : ℝ)^5015 ≤ (461271972501/1000000000000 : ℝ)^3991 := by
    have hnat : (5402226793 : ℕ)^5015*1000000000000^3991 ≤ 461271972501^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402226793 10000000000 461271972501 1000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625292707/5000000000 : ℝ), (-30381303/200000000 : ℝ), (5402226793/10000000000 : ℝ)] ![(44506083900043/100000000000000 : ℝ), (585419926919/6250000000000 : ℝ), (461271972501/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625292707/5000000000 : ℝ)|^5015 ≤ (44506083900043/100000000000000 : ℝ)^3991
        have hw : |(2625292707/5000000000 : ℝ)|=(2625292707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30381303/200000000 : ℝ)|^5015 ≤ (585419926919/6250000000000 : ℝ)^3991
        have hw : |(-30381303/200000000 : ℝ)|=(30381303/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402226793/10000000000 : ℝ)|^5015 ≤ (461271972501/1000000000000 : ℝ)^3991
        have hw : |(5402226793/10000000000 : ℝ)|=(5402226793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_2 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250585573/10000000000 : ℝ)*x 0 + (2701113341/5000000000 : ℝ)*x 1 + (-303813017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250585573/10000000000 : ℝ)^5015 ≤ (44506085593593/100000000000000 : ℝ)^3991 := by
    have hnat : (5250585573 : ℕ)^5015*100000000000000^3991 ≤ 44506085593593^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250585573 10000000000 44506085593593 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701113341/5000000000 : ℝ)^5015 ≤ (23063598029571/50000000000000 : ℝ)^3991 := by
    have hnat : (2701113341 : ℕ)^5015*50000000000000^3991 ≤ 23063598029571^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701113341 5000000000 23063598029571 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303813017/2000000000 : ℝ)^5015 ≤ (9366718327071/100000000000000 : ℝ)^3991 := by
    have hnat : (303813017 : ℕ)^5015*100000000000000^3991 ≤ 9366718327071^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303813017 2000000000 9366718327071 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250585573/10000000000 : ℝ), (2701113341/5000000000 : ℝ), (-303813017/2000000000 : ℝ)] ![(44506085593593/100000000000000 : ℝ), (23063598029571/50000000000000 : ℝ), (9366718327071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250585573/10000000000 : ℝ)|^5015 ≤ (44506085593593/100000000000000 : ℝ)^3991
        have hw : |(5250585573/10000000000 : ℝ)|=(5250585573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701113341/5000000000 : ℝ)|^5015 ≤ (23063598029571/50000000000000 : ℝ)^3991
        have hw : |(2701113341/5000000000 : ℝ)|=(2701113341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-303813017/2000000000 : ℝ)|^5015 ≤ (9366718327071/100000000000000 : ℝ)^3991
        have hw : |(-303813017/2000000000 : ℝ)|=(303813017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_3 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (887610817/2000000000 : ℝ)*x 0 + (252294297/625000000 : ℝ)*x 1 + (4036708831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887610817/2000000000 : ℝ)^5015 ≤ (36030494145447/100000000000000 : ℝ)^3991 := by
    have hnat : (887610817 : ℕ)^5015*100000000000000^3991 ≤ 36030494145447^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887610817 2000000000 36030494145447 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252294297/625000000 : ℝ)^5015 ≤ (15992376264539/50000000000000 : ℝ)^3991 := by
    have hnat : (252294297 : ℕ)^5015*50000000000000^3991 ≤ 15992376264539^3991*625000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252294297 625000000 15992376264539 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036708831/10000000000 : ℝ)^5015 ≤ (15992376657819/50000000000000 : ℝ)^3991 := by
    have hnat : (4036708831 : ℕ)^5015*50000000000000^3991 ≤ 15992376657819^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036708831 10000000000 15992376657819 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(887610817/2000000000 : ℝ), (252294297/625000000 : ℝ), (4036708831/10000000000 : ℝ)] ![(36030494145447/100000000000000 : ℝ), (15992376264539/50000000000000 : ℝ), (15992376657819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(887610817/2000000000 : ℝ)|^5015 ≤ (36030494145447/100000000000000 : ℝ)^3991
        have hw : |(887610817/2000000000 : ℝ)|=(887610817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252294297/625000000 : ℝ)|^5015 ≤ (15992376264539/50000000000000 : ℝ)^3991
        have hw : |(252294297/625000000 : ℝ)|=(252294297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036708831/10000000000 : ℝ)|^5015 ≤ (15992376657819/50000000000000 : ℝ)^3991
        have hw : |(4036708831/10000000000 : ℝ)|=(4036708831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_4 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1815725937/10000000000 : ℝ)*x 0 + (5216171699/10000000000 : ℝ)*x 1 + (2608085597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1815725937/10000000000 : ℝ)^5015 ≤ (11720318775641/100000000000000 : ℝ)^3991 := by
    have hnat : (1815725937 : ℕ)^5015*100000000000000^3991 ≤ 11720318775641^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815725937 10000000000 11720318775641 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216171699/10000000000 : ℝ)^5015 ≤ (44139843287377/100000000000000 : ℝ)^3991 := by
    have hnat : (5216171699 : ℕ)^5015*100000000000000^3991 ≤ 44139843287377^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216171699 10000000000 44139843287377 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608085597/5000000000 : ℝ)^5015 ≤ (44139837917559/100000000000000 : ℝ)^3991 := by
    have hnat : (2608085597 : ℕ)^5015*100000000000000^3991 ≤ 44139837917559^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608085597 5000000000 44139837917559 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1815725937/10000000000 : ℝ), (5216171699/10000000000 : ℝ), (2608085597/5000000000 : ℝ)] ![(11720318775641/100000000000000 : ℝ), (44139843287377/100000000000000 : ℝ), (44139837917559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1815725937/10000000000 : ℝ)|^5015 ≤ (11720318775641/100000000000000 : ℝ)^3991
        have hw : |(-1815725937/10000000000 : ℝ)|=(1815725937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216171699/10000000000 : ℝ)|^5015 ≤ (44139843287377/100000000000000 : ℝ)^3991
        have hw : |(5216171699/10000000000 : ℝ)|=(5216171699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608085597/5000000000 : ℝ)|^5015 ≤ (44139837917559/100000000000000 : ℝ)^3991
        have hw : |(2608085597/5000000000 : ℝ)|=(2608085597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_5 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688942447/5000000000 : ℝ)*x 0 + (-49983809/312500000 : ℝ)*x 1 + (1043234353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688942447/5000000000 : ℝ)^5015 ≤ (45866175606427/100000000000000 : ℝ)^3991 := by
    have hnat : (2688942447 : ℕ)^5015*100000000000000^3991 ≤ 45866175606427^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688942447 5000000000 45866175606427 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49983809/312500000 : ℝ)^5015 ≤ (4996990188583/50000000000000 : ℝ)^3991 := by
    have hnat : (49983809 : ℕ)^5015*50000000000000^3991 ≤ 4996990188583^3991*312500000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49983809 312500000 4996990188583 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043234353/2000000000 : ℝ)^5015 ≤ (22069921994587/50000000000000 : ℝ)^3991 := by
    have hnat : (1043234353 : ℕ)^5015*50000000000000^3991 ≤ 22069921994587^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043234353 2000000000 22069921994587 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688942447/5000000000 : ℝ), (-49983809/312500000 : ℝ), (1043234353/2000000000 : ℝ)] ![(45866175606427/100000000000000 : ℝ), (4996990188583/50000000000000 : ℝ), (22069921994587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688942447/5000000000 : ℝ)|^5015 ≤ (45866175606427/100000000000000 : ℝ)^3991
        have hw : |(2688942447/5000000000 : ℝ)|=(2688942447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49983809/312500000 : ℝ)|^5015 ≤ (4996990188583/50000000000000 : ℝ)^3991
        have hw : |(-49983809/312500000 : ℝ)|=(49983809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043234353/2000000000 : ℝ)|^5015 ≤ (22069921994587/50000000000000 : ℝ)^3991
        have hw : |(1043234353/2000000000 : ℝ)|=(1043234353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_6 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537788519/1000000000 : ℝ)*x 0 + (2608085657/5000000000 : ℝ)*x 1 + (-99967631/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537788519/1000000000 : ℝ)^5015 ≤ (45866178778637/100000000000000 : ℝ)^3991 := by
    have hnat : (537788519 : ℕ)^5015*100000000000000^3991 ≤ 45866178778637^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537788519 1000000000 45866178778637 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608085657/5000000000 : ℝ)^5015 ≤ (11034959798389/25000000000000 : ℝ)^3991 := by
    have hnat : (2608085657 : ℕ)^5015*25000000000000^3991 ≤ 11034959798389^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608085657 5000000000 11034959798389 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99967631/625000000 : ℝ)^5015 ≤ (4996991005131/50000000000000 : ℝ)^3991 := by
    have hnat : (99967631 : ℕ)^5015*50000000000000^3991 ≤ 4996991005131^3991*625000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99967631 625000000 4996991005131 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537788519/1000000000 : ℝ), (2608085657/5000000000 : ℝ), (-99967631/625000000 : ℝ)] ![(45866178778637/100000000000000 : ℝ), (11034959798389/25000000000000 : ℝ), (4996991005131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537788519/1000000000 : ℝ)|^5015 ≤ (45866178778637/100000000000000 : ℝ)^3991
        have hw : |(537788519/1000000000 : ℝ)|=(537788519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608085657/5000000000 : ℝ)|^5015 ≤ (11034959798389/25000000000000 : ℝ)^3991
        have hw : |(2608085657/5000000000 : ℝ)|=(2608085657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99967631/625000000 : ℝ)|^5015 ≤ (4996991005131/50000000000000 : ℝ)^3991
        have hw : |(-99967631/625000000 : ℝ)|=(99967631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_7 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3880520693/10000000000 : ℝ)*x 0 + (539395029/1250000000 : ℝ)*x 1 + (4315159699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3880520693/10000000000 : ℝ)^5015 ≤ (7609366812153/25000000000000 : ℝ)^3991 := by
    have hnat : (3880520693 : ℕ)^5015*25000000000000^3991 ≤ 7609366812153^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880520693 10000000000 7609366812153 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539395029/1250000000 : ℝ)^5015 ≤ (6956253813193/20000000000000 : ℝ)^3991 := by
    have hnat : (539395029 : ℕ)^5015*20000000000000^3991 ≤ 6956253813193^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539395029 1250000000 6956253813193 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4315159699/10000000000 : ℝ)^5015 ≤ (34781263667567/100000000000000 : ℝ)^3991 := by
    have hnat : (4315159699 : ℕ)^5015*100000000000000^3991 ≤ 34781263667567^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315159699 10000000000 34781263667567 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3880520693/10000000000 : ℝ), (539395029/1250000000 : ℝ), (4315159699/10000000000 : ℝ)] ![(7609366812153/25000000000000 : ℝ), (6956253813193/20000000000000 : ℝ), (34781263667567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3880520693/10000000000 : ℝ)|^5015 ≤ (7609366812153/25000000000000 : ℝ)^3991
        have hw : |(3880520693/10000000000 : ℝ)|=(3880520693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539395029/1250000000 : ℝ)|^5015 ≤ (6956253813193/20000000000000 : ℝ)^3991
        have hw : |(539395029/1250000000 : ℝ)|=(539395029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4315159699/10000000000 : ℝ)|^5015 ≤ (34781263667567/100000000000000 : ℝ)^3991
        have hw : |(4315159699/10000000000 : ℝ)|=(4315159699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_8 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-341359357/2000000000 : ℝ)*x 0 + (5081826159/10000000000 : ℝ)*x 1 + (5431384099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341359357/2000000000 : ℝ)^5015 ≤ (10843690174753/100000000000000 : ℝ)^3991 := by
    have hnat : (341359357 : ℕ)^5015*100000000000000^3991 ≤ 10843690174753^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341359357 2000000000 10843690174753 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081826159/10000000000 : ℝ)^5015 ≤ (5339507156893/12500000000000 : ℝ)^3991 := by
    have hnat : (5081826159 : ℕ)^5015*12500000000000^3991 ≤ 5339507156893^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081826159 10000000000 5339507156893 12500000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431384099/10000000000 : ℝ)^5015 ≤ (46440252551939/100000000000000 : ℝ)^3991 := by
    have hnat : (5431384099 : ℕ)^5015*100000000000000^3991 ≤ 46440252551939^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431384099 10000000000 46440252551939 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341359357/2000000000 : ℝ), (5081826159/10000000000 : ℝ), (5431384099/10000000000 : ℝ)] ![(10843690174753/100000000000000 : ℝ), (5339507156893/12500000000000 : ℝ), (46440252551939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341359357/2000000000 : ℝ)|^5015 ≤ (10843690174753/100000000000000 : ℝ)^3991
        have hw : |(-341359357/2000000000 : ℝ)|=(341359357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081826159/10000000000 : ℝ)|^5015 ≤ (5339507156893/12500000000000 : ℝ)^3991
        have hw : |(5081826159/10000000000 : ℝ)|=(5081826159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431384099/10000000000 : ℝ)|^5015 ≤ (46440252551939/100000000000000 : ℝ)^3991
        have hw : |(5431384099/10000000000 : ℝ)|=(5431384099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_9 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230639591/10000000000 : ℝ)*x 0 + (-60242097/400000000 : ℝ)*x 1 + (1357846099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230639591/10000000000 : ℝ)^5015 ≤ (22146869722593/50000000000000 : ℝ)^3991 := by
    have hnat : (5230639591 : ℕ)^5015*50000000000000^3991 ≤ 22146869722593^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230639591 10000000000 22146869722593 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60242097/400000000 : ℝ)^5015 ≤ (1853200959223/20000000000000 : ℝ)^3991 := by
    have hnat : (60242097 : ℕ)^5015*20000000000000^3991 ≤ 1853200959223^3991*400000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60242097 400000000 1853200959223 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357846099/2500000000 : ℝ)^5015 ≤ (46440255742961/100000000000000 : ℝ)^3991 := by
    have hnat : (1357846099 : ℕ)^5015*100000000000000^3991 ≤ 46440255742961^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357846099 2500000000 46440255742961 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230639591/10000000000 : ℝ), (-60242097/400000000 : ℝ), (1357846099/2500000000 : ℝ)] ![(22146869722593/50000000000000 : ℝ), (1853200959223/20000000000000 : ℝ), (46440255742961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230639591/10000000000 : ℝ)|^5015 ≤ (22146869722593/50000000000000 : ℝ)^3991
        have hw : |(5230639591/10000000000 : ℝ)|=(5230639591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-60242097/400000000 : ℝ)|^5015 ≤ (1853200959223/20000000000000 : ℝ)^3991
        have hw : |(-60242097/400000000 : ℝ)|=(60242097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357846099/2500000000 : ℝ)|^5015 ≤ (46440255742961/100000000000000 : ℝ)^3991
        have hw : |(1357846099/2500000000 : ℝ)|=(1357846099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_10 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230639979/10000000000 : ℝ)*x 0 + (2715692103/5000000000 : ℝ)*x 1 + (-376513039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230639979/10000000000 : ℝ)^5015 ≤ (553671794673/1250000000000 : ℝ)^3991 := by
    have hnat : (5230639979 : ℕ)^5015*1250000000000^3991 ≤ 553671794673^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230639979 10000000000 553671794673 1250000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715692103/5000000000 : ℝ)^5015 ≤ (23220126850783/50000000000000 : ℝ)^3991 := by
    have hnat : (2715692103 : ℕ)^5015*50000000000000^3991 ≤ 23220126850783^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715692103 5000000000 23220126850783 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376513039/2500000000 : ℝ)^5015 ≤ (289562584889/3125000000000 : ℝ)^3991 := by
    have hnat : (376513039 : ℕ)^5015*3125000000000^3991 ≤ 289562584889^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376513039 2500000000 289562584889 3125000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230639979/10000000000 : ℝ), (2715692103/5000000000 : ℝ), (-376513039/2500000000 : ℝ)] ![(553671794673/1250000000000 : ℝ), (23220126850783/50000000000000 : ℝ), (289562584889/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230639979/10000000000 : ℝ)|^5015 ≤ (553671794673/1250000000000 : ℝ)^3991
        have hw : |(5230639979/10000000000 : ℝ)|=(5230639979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715692103/5000000000 : ℝ)|^5015 ≤ (23220126850783/50000000000000 : ℝ)^3991
        have hw : |(2715692103/5000000000 : ℝ)|=(2715692103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-376513039/2500000000 : ℝ)|^5015 ≤ (289562584889/3125000000000 : ℝ)^3991
        have hw : |(-376513039/2500000000 : ℝ)|=(376513039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_11 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (90461229/200000000 : ℝ)*x 0 + (3992991413/10000000000 : ℝ)*x 1 + (998247813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90461229/200000000 : ℝ)^5015 ≤ (7379964661569/20000000000000 : ℝ)^3991 := by
    have hnat : (90461229 : ℕ)^5015*20000000000000^3991 ≤ 7379964661569^3991*200000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90461229 200000000 7379964661569 20000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3992991413/10000000000 : ℝ)^5015 ≤ (31550089134257/100000000000000 : ℝ)^3991 := by
    have hnat : (3992991413 : ℕ)^5015*100000000000000^3991 ≤ 31550089134257^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992991413 10000000000 31550089134257 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998247813/2500000000 : ℝ)^5015 ≤ (1577504376787/5000000000000 : ℝ)^3991 := by
    have hnat : (998247813 : ℕ)^5015*5000000000000^3991 ≤ 1577504376787^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998247813 2500000000 1577504376787 5000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90461229/200000000 : ℝ), (3992991413/10000000000 : ℝ), (998247813/2500000000 : ℝ)] ![(7379964661569/20000000000000 : ℝ), (31550089134257/100000000000000 : ℝ), (1577504376787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90461229/200000000 : ℝ)|^5015 ≤ (7379964661569/20000000000000 : ℝ)^3991
        have hw : |(90461229/200000000 : ℝ)|=(90461229/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3992991413/10000000000 : ℝ)|^5015 ≤ (31550089134257/100000000000000 : ℝ)^3991
        have hw : |(3992991413/10000000000 : ℝ)|=(3992991413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998247813/2500000000 : ℝ)|^5015 ≤ (1577504376787/5000000000000 : ℝ)^3991
        have hw : |(998247813/2500000000 : ℝ)|=(998247813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_12 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1412750519/10000000000 : ℝ)*x 0 + (691451027/1250000000 : ℝ)*x 1 + (5196416527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1412750519/10000000000 : ℝ)^5015 ≤ (8550501174193/100000000000000 : ℝ)^3991 := by
    have hnat : (1412750519 : ℕ)^5015*100000000000000^3991 ≤ 8550501174193^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412750519 10000000000 8550501174193 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (691451027/1250000000 : ℝ)^5015 ≤ (11879904017009/25000000000000 : ℝ)^3991 := by
    have hnat : (691451027 : ℕ)^5015*25000000000000^3991 ≤ 11879904017009^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691451027 1250000000 11879904017009 25000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196416527/10000000000 : ℝ)^5015 ≤ (686404417979/1562500000000 : ℝ)^3991 := by
    have hnat : (5196416527 : ℕ)^5015*1562500000000^3991 ≤ 686404417979^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196416527 10000000000 686404417979 1562500000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1412750519/10000000000 : ℝ), (691451027/1250000000 : ℝ), (5196416527/10000000000 : ℝ)] ![(8550501174193/100000000000000 : ℝ), (11879904017009/25000000000000 : ℝ), (686404417979/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1412750519/10000000000 : ℝ)|^5015 ≤ (8550501174193/100000000000000 : ℝ)^3991
        have hw : |(-1412750519/10000000000 : ℝ)|=(1412750519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(691451027/1250000000 : ℝ)|^5015 ≤ (11879904017009/25000000000000 : ℝ)^3991
        have hw : |(691451027/1250000000 : ℝ)|=(691451027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196416527/10000000000 : ℝ)|^5015 ≤ (686404417979/1562500000000 : ℝ)^3991
        have hw : |(5196416527/10000000000 : ℝ)|=(5196416527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_13 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695706551/5000000000 : ℝ)*x 0 + (-200968363/1250000000 : ℝ)*x 1 + (5196416393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695706551/5000000000 : ℝ)^5015 ≤ (368089625361/800000000000 : ℝ)^3991 := by
    have hnat : (2695706551 : ℕ)^5015*800000000000^3991 ≤ 368089625361^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695706551 5000000000 368089625361 800000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200968363/1250000000 : ℝ)^5015 ≤ (5029457738147/50000000000000 : ℝ)^3991 := by
    have hnat : (200968363 : ℕ)^5015*50000000000000^3991 ≤ 5029457738147^3991*1250000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200968363 1250000000 5029457738147 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196416393/10000000000 : ℝ)^5015 ≤ (2196494066359/5000000000000 : ℝ)^3991 := by
    have hnat : (5196416393 : ℕ)^5015*5000000000000^3991 ≤ 2196494066359^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196416393 10000000000 2196494066359 5000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695706551/5000000000 : ℝ), (-200968363/1250000000 : ℝ), (5196416393/10000000000 : ℝ)] ![(368089625361/800000000000 : ℝ), (5029457738147/50000000000000 : ℝ), (2196494066359/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695706551/5000000000 : ℝ)|^5015 ≤ (368089625361/800000000000 : ℝ)^3991
        have hw : |(2695706551/5000000000 : ℝ)|=(2695706551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200968363/1250000000 : ℝ)|^5015 ≤ (5029457738147/50000000000000 : ℝ)^3991
        have hw : |(-200968363/1250000000 : ℝ)|=(200968363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196416393/10000000000 : ℝ)|^5015 ≤ (2196494066359/5000000000000 : ℝ)^3991
        have hw : |(5196416393/10000000000 : ℝ)|=(5196416393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_14 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078282507/2000000000 : ℝ)*x 0 + (1299104171/2500000000 : ℝ)*x 1 + (-803873643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078282507/2000000000 : ℝ)^5015 ≤ (4601119708971/10000000000000 : ℝ)^3991 := by
    have hnat : (1078282507 : ℕ)^5015*10000000000000^3991 ≤ 4601119708971^3991*2000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078282507 2000000000 4601119708971 10000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299104171/2500000000 : ℝ)^5015 ≤ (2196494220923/5000000000000 : ℝ)^3991 := by
    have hnat : (1299104171 : ℕ)^5015*5000000000000^3991 ≤ 2196494220923^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299104171 2500000000 2196494220923 5000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803873643/5000000000 : ℝ)^5015 ≤ (5029459239753/50000000000000 : ℝ)^3991 := by
    have hnat : (803873643 : ℕ)^5015*50000000000000^3991 ≤ 5029459239753^3991*5000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803873643 5000000000 5029459239753 50000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078282507/2000000000 : ℝ), (1299104171/2500000000 : ℝ), (-803873643/5000000000 : ℝ)] ![(4601119708971/10000000000000 : ℝ), (2196494220923/5000000000000 : ℝ), (5029459239753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078282507/2000000000 : ℝ)|^5015 ≤ (4601119708971/10000000000000 : ℝ)^3991
        have hw : |(1078282507/2000000000 : ℝ)|=(1078282507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299104171/2500000000 : ℝ)|^5015 ≤ (2196494220923/5000000000000 : ℝ)^3991
        have hw : |(1299104171/2500000000 : ℝ)|=(1299104171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-803873643/5000000000 : ℝ)|^5015 ≤ (5029459239753/50000000000000 : ℝ)^3991
        have hw : |(-803873643/5000000000 : ℝ)|=(803873643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1674_box_15 (p : ℝ) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (381969323/1000000000 : ℝ)*x 0 + (1086167711/2500000000 : ℝ)*x 1 + (4344670807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381969323/1000000000 : ℝ)^5015 ≤ (1864947025033/6250000000000 : ℝ)^3991 := by
    have hnat : (381969323 : ℕ)^5015*6250000000000^3991 ≤ 1864947025033^3991*1000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381969323 1000000000 1864947025033 6250000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086167711/2500000000 : ℝ)^5015 ≤ (35080423977901/100000000000000 : ℝ)^3991 := by
    have hnat : (1086167711 : ℕ)^5015*100000000000000^3991 ≤ 35080423977901^3991*2500000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086167711 2500000000 35080423977901 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4344670807/10000000000 : ℝ)^5015 ≤ (35080423602497/100000000000000 : ℝ)^3991 := by
    have hnat : (4344670807 : ℕ)^5015*100000000000000^3991 ≤ 35080423602497^3991*10000000000^5015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344670807 10000000000 35080423602497 100000000000000 5015 3991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5015/1024 : ℝ)) 5015 3991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(381969323/1000000000 : ℝ), (1086167711/2500000000 : ℝ), (4344670807/10000000000 : ℝ)] ![(1864947025033/6250000000000 : ℝ), (35080423977901/100000000000000 : ℝ), (35080423602497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(381969323/1000000000 : ℝ)|^5015 ≤ (1864947025033/6250000000000 : ℝ)^3991
        have hw : |(381969323/1000000000 : ℝ)|=(381969323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086167711/2500000000 : ℝ)|^5015 ≤ (35080423977901/100000000000000 : ℝ)^3991
        have hw : |(1086167711/2500000000 : ℝ)|=(1086167711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4344670807/10000000000 : ℝ)|^5015 ≤ (35080423602497/100000000000000 : ℝ)^3991
        have hw : |(4344670807/10000000000 : ℝ)|=(4344670807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1674_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65173/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14721/25000 : ℝ) ∧ (40811/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88453/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10787/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10787/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10787/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10787/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10787/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10787/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10787/100000 : ℝ) ^ (5011/1024 : ℝ) ≤ (1851171191923379/100000000000000000000 : ℝ) := by
    have hpowers : (10787/100000 : ℝ)^5011 ≤ (1851171191923379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10787 : ℕ)^5011*100000000000000000000^1024 ≤ 1851171191923379^1024*100000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10787 100000 1851171191923379 100000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10787/100000 : ℝ)) (X := (1851171191923379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16219/100000 : ℝ) ^ (5011/1024 : ℝ) ≤ (3405254786235681/25000000000000000000 : ℝ) := by
    have hpowers : (16219/100000 : ℝ)^5011 ≤ (3405254786235681/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16219 : ℕ)^5011*25000000000000000000^1024 ≤ 3405254786235681^1024*100000^5011 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16219 100000 3405254786235681 25000000000000000000 5011 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16219/100000 : ℝ)) (X := (3405254786235681/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001851171191923379/50000000000000000000 : ℝ) ≤ (10000075656411143/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (50001851171191923379/50000000000000000000 : ℝ)^1024 ≤ (10000075656411143/10000000000000000 : ℝ)^5011 := by
      have hnat : (50001851171191923379 : ℕ)^1024*10000000000000000^5011 ≤ 10000075656411143^5011*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001851171191923379 50000000000000000000 10000075656411143 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000075656411143/10000000000000000 : ℝ)) (X := (50001851171191923379/50000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015472190336866103/100000000000000000000 : ℝ) ≤ (10000316155413919/10000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (100015472190336866103/100000000000000000000 : ℝ)^1024 ≤ (10000316155413919/10000000000000000 : ℝ)^5011 := by
      have hnat : (100015472190336866103 : ℕ)^1024*10000000000000000^5011 ≤ 10000316155413919^5011*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015472190336866103 100000000000000000000 10000316155413919 10000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000316155413919/10000000000000000 : ℝ)) (X := (100015472190336866103/100000000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503405254786235681/12500000000000000000 : ℝ) ≤ (2000111330883339/2000000000000000 : ℝ) ^ (5011/1024 : ℝ) := by
    have hpowers : (12503405254786235681/12500000000000000000 : ℝ)^1024 ≤ (2000111330883339/2000000000000000 : ℝ)^5011 := by
      have hnat : (12503405254786235681 : ℕ)^1024*2000000000000000^5011 ≤ 2000111330883339^5011*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503405254786235681 12500000000000000000 2000111330883339 2000000000000000 1024 5011 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000111330883339/2000000000000000 : ℝ)) (X := (12503405254786235681/12500000000000000000 : ℝ)) (by norm_num) 5011 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1851171191923379/100000000000000000000 : ℝ) ≤ ((969914686431061417/970000000000000000 : ℝ)+2*(30062375347/67900000000000 : ℝ)*(10787/100000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (969914686431061417/970000000000000000 : ℝ)+2*(30062375347/67900000000000 : ℝ)*(10787/100000 : ℝ)=(10000075656411143/10000000000000000 : ℝ) by norm_num, show 1+2*(1851171191923379/100000000000000000000 : ℝ)=(50001851171191923379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3405254786235681/25000000000000000000 : ℝ)+(1851171191923379/100000000000000000000 : ℝ) ≤ ((969914686431061417/970000000000000000 : ℝ)+(30062375347/67900000000000 : ℝ)*((16219/100000 : ℝ)+(10787/100000 : ℝ)))^(5011/1024 : ℝ) := by
    rw [show (969914686431061417/970000000000000000 : ℝ)+(30062375347/67900000000000 : ℝ)*((16219/100000 : ℝ)+(10787/100000 : ℝ))=(10000316155413919/10000000000000000 : ℝ) by norm_num, show 1+(3405254786235681/25000000000000000000 : ℝ)+(1851171191923379/100000000000000000000 : ℝ)=(100015472190336866103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3405254786235681/25000000000000000000 : ℝ) ≤ ((969914686431061417/970000000000000000 : ℝ)+2*(30062375347/67900000000000 : ℝ)*(16219/100000 : ℝ))^(5011/1024 : ℝ) := by
    rw [show (969914686431061417/970000000000000000 : ℝ)+2*(30062375347/67900000000000 : ℝ)*(16219/100000 : ℝ)=(2000111330883339/2000000000000000 : ℝ) by norm_num, show 1+2*(3405254786235681/25000000000000000000 : ℝ)=(12503405254786235681/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (969914686431061417/970000000000000000 : ℝ)*(X 1 0+X 2 0)+(30062375347/67900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (16219/100000 : ℝ)) (c := (969914686431061417/970000000000000000 : ℝ)) (alpha := (30062375347/67900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (969914686431061417/970000000000000000 : ℝ)*(X 0 1+X 2 1)+(30062375347/67900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (16219/100000 : ℝ)) (c := (969914686431061417/970000000000000000 : ℝ)) (alpha := (30062375347/67900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (969914686431061417/970000000000000000 : ℝ)*(X 0 2+X 1 2)+(30062375347/67900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5011/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (16219/100000 : ℝ)) (c := (969914686431061417/970000000000000000 : ℝ)) (alpha := (30062375347/67900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261171887/2000000000 : ℝ)*X 0 0+(2701113339/5000000000 : ℝ)*X 0 1+(2701113327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625292707/5000000000 : ℝ)*X 1 0+(-30381303/200000000 : ℝ)*X 1 1+(5402226793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250585573/10000000000 : ℝ)*X 2 0+(2701113341/5000000000 : ℝ)*X 2 1+(-303813017/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((887610817/2000000000 : ℝ)*X 0 0+(252294297/625000000 : ℝ)*X 0 1+(4036708831/10000000000 : ℝ)*X 0 2+(887610817/2000000000 : ℝ)*X 1 0+(252294297/625000000 : ℝ)*X 1 1+(4036708831/10000000000 : ℝ)*X 1 2+(887610817/2000000000 : ℝ)*X 2 0+(252294297/625000000 : ℝ)*X 2 1+(4036708831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1815725937/10000000000 : ℝ)*X 0 0+(5216171699/10000000000 : ℝ)*X 0 1+(2608085597/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2688942447/5000000000 : ℝ)*X 1 0+(-49983809/312500000 : ℝ)*X 1 1+(1043234353/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537788519/1000000000 : ℝ)*X 2 0+(2608085657/5000000000 : ℝ)*X 2 1+(-99967631/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3880520693/10000000000 : ℝ)*X 0 0+(539395029/1250000000 : ℝ)*X 0 1+(4315159699/10000000000 : ℝ)*X 0 2+(3880520693/10000000000 : ℝ)*X 1 0+(539395029/1250000000 : ℝ)*X 1 1+(4315159699/10000000000 : ℝ)*X 1 2+(3880520693/10000000000 : ℝ)*X 2 0+(539395029/1250000000 : ℝ)*X 2 1+(4315159699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-341359357/2000000000 : ℝ)*X 0 0+(5081826159/10000000000 : ℝ)*X 0 1+(5431384099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230639591/10000000000 : ℝ)*X 1 0+(-60242097/400000000 : ℝ)*X 1 1+(1357846099/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230639979/10000000000 : ℝ)*X 2 0+(2715692103/5000000000 : ℝ)*X 2 1+(-376513039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((90461229/200000000 : ℝ)*X 0 0+(3992991413/10000000000 : ℝ)*X 0 1+(998247813/2500000000 : ℝ)*X 0 2+(90461229/200000000 : ℝ)*X 1 0+(3992991413/10000000000 : ℝ)*X 1 1+(998247813/2500000000 : ℝ)*X 1 2+(90461229/200000000 : ℝ)*X 2 0+(3992991413/10000000000 : ℝ)*X 2 1+(998247813/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1412750519/10000000000 : ℝ)*X 0 0+(691451027/1250000000 : ℝ)*X 0 1+(5196416527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2695706551/5000000000 : ℝ)*X 1 0+(-200968363/1250000000 : ℝ)*X 1 1+(5196416393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1078282507/2000000000 : ℝ)*X 2 0+(1299104171/2500000000 : ℝ)*X 2 1+(-803873643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((381969323/1000000000 : ℝ)*X 0 0+(1086167711/2500000000 : ℝ)*X 0 1+(4344670807/10000000000 : ℝ)*X 0 2+(381969323/1000000000 : ℝ)*X 1 0+(1086167711/2500000000 : ℝ)*X 1 1+(4344670807/10000000000 : ℝ)*X 1 2+(381969323/1000000000 : ℝ)*X 2 0+(1086167711/2500000000 : ℝ)*X 2 1+(4344670807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1674_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65173/100000 : ℝ) ≤ (-7901977233167832759517271785131/12125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45504589/100000000000000 : ℝ)*(upper1) + (68997943/100000000000000 : ℝ)*(upper3) + (7019797/12500000000000 : ℝ)*(upper5) + (451060992664119/25000000000000 : ℝ)*(major0) + (451060992664119/25000000000000 : ℝ)*(major1) + (451060992664119/25000000000000 : ℝ)*(major2) + (4957663441/100000000000000 : ℝ)*(sp2) + (2810721719/100000000000000 : ℝ)*(sp3) + (661449108010009/25000000000000 : ℝ)*(sp4) + (661447522282133/25000000000000 : ℝ)*(sp5) + (264579637083517/10000000000000 : ℝ)*(sp6) + (984407450843591/100000000000000 : ℝ)*(sp7) + (195858343/4000000000000 : ℝ)*(sp8) + (5619685039/50000000000000 : ℝ)*(sp13) + (98441026156531/10000000000000 : ℝ)*(f.failure) + (264580132849861/10000000000000 : ℝ)*(f.sum) + (10664693383627/3395000000000000000000000000 : ℝ)*base65 + (1828798817915073639/169750000000000000000000000000000 : ℝ)*base68 + (28809531804426361/169750000000000000000000000000000 : ℝ)*base69 + (90768836038176361/169750000000000000000000000000000 : ℝ)*base71 + (2172962303317/848750000000000000000000000 : ℝ)*base74 + (358571125014323639/169750000000000000000000000000000 : ℝ)*base76 + (784311329034573639/169750000000000000000000000000000 : ℝ)*base78 + (1117451521536823639/169750000000000000000000000000000 : ℝ)*base80 + (53049705929937/3395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4495459/1000000000000000000000 : ℝ)*base90 + (4495459/1000000000000000000000 : ℝ)*base92 + (4495459/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14721/25000 : ℝ) ≤ (1999197429429263614972792510557/3395000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175649/100000000000000 : ℝ)*(upper0) + (27633429/100000000000000 : ℝ)*(lower1) + (40711153/100000000000000 : ℝ)*(upper4) + (18980472336467/1000000000000 : ℝ)*(major0) + (18980472336467/1000000000000 : ℝ)*(major1) + (18980472336467/1000000000000 : ℝ)*(major2) + (342609424343349/12500000000000 : ℝ)*(sp0) + (548174999548567/20000000000000 : ℝ)*(sp1) + (685218805774743/25000000000000 : ℝ)*(sp2) + (517794924841557/50000000000000 : ℝ)*(sp3) + (540038533/100000000000000 : ℝ)*(sp5) + (78670599/25000000000000 : ℝ)*(sp6) + (8939661/6250000000000 : ℝ)*(sp8) + (239088319/100000000000000 : ℝ)*(sp11) + (129448761096429/12500000000000 : ℝ)*(f.failure) + (342609442222671/12500000000000 : ℝ)*(f.sum) + (4022772137/33950000000000000000000000 : ℝ)*base65 + (34784796082193827/6790000000000000000000000000000 : ℝ)*base68 + (54085079648603827/6790000000000000000000000000000 : ℝ)*base70 + (25262794747823827/6790000000000000000000000000000 : ℝ)*base72 + (2027742322621/679000000000000000000000000 : ℝ)*base73 + (71673881443923827/6790000000000000000000000000000 : ℝ)*base76 + (56251112204983827/6790000000000000000000000000000 : ℝ)*base78 + (4539207473713827/6790000000000000000000000000000 : ℝ)*base80 + (2077297579507/339500000000000000000000000 : ℝ)*base82 + (6889981/1250000000000000000000 : ℝ)*base90 + (6889981/1250000000000000000000 : ℝ)*base92 + (6889981/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40811/50000 : ℝ) ≤ (2771151716528613480379804443/3395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3283839/20000000000000 : ℝ)*(upper0) + (7380579/25000000000000 : ℝ)*(lower1) + (32949109/25000000000000 : ℝ)*(upper4) + (992843204816159/50000000000000 : ℝ)*(major0) + (992843204816159/50000000000000 : ℝ)*(major1) + (992843204816159/50000000000000 : ℝ)*(major2) + (729157673/100000000000000 : ℝ)*(sp0) + (4935953729/25000000000000 : ℝ)*(sp1) + (3771490353/12500000000000 : ℝ)*(sp2) + (1660281173/10000000000000 : ℝ)*(sp3) + (286075718430301/10000000000000 : ℝ)*(sp8) + (1430369084822883/50000000000000 : ℝ)*(sp9) + (1430363870768929/50000000000000 : ℝ)*(sp10) + (541695068449821/50000000000000 : ℝ)*(sp11) + (1083406739711371/100000000000000 : ℝ)*(f.failure) + (1430378956730341/50000000000000 : ℝ)*(f.sum) + (23482694006929/3395000000000000000000000000 : ℝ)*base66 + (950977895326438879/339500000000000000000000000000000 : ℝ)*base68 + (1984585494588438879/339500000000000000000000000000000 : ℝ)*base70 + (785641697481438879/339500000000000000000000000000000 : ℝ)*base72 + (19171698504863/1697500000000000000000000000 : ℝ)*base73 + (532108452927561121/339500000000000000000000000000000 : ℝ)*base75 + (704666136260561121/339500000000000000000000000000000 : ℝ)*base77 + (678478892709561121/339500000000000000000000000000000 : ℝ)*base79 + (619054367053/424375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (76964219/10000000000000000000000 : ℝ)*base90 + (76964219/10000000000000000000000 : ℝ)*base92 + (76964219/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-88453/100000 : ℝ) ≤ (-300288164951387503600818829208601/339500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43663853/25000000000000 : ℝ)*(upper3) + (66140269/50000000000000 : ℝ)*(lower4) + (34063899/100000000000000 : ℝ)*(upper5) + (2031016082917231/100000000000000 : ℝ)*(major0) + (2031016082917231/100000000000000 : ℝ)*(major1) + (2031016082917231/100000000000000 : ℝ)*(major2) + (1927874547/50000000000000 : ℝ)*(sp4) + (112500823343/100000000000000 : ℝ)*(sp5) + (42623493661/50000000000000 : ℝ)*(sp6) + (806087927/1562500000000 : ℝ)*(sp7) + (1491686352048607/50000000000000 : ℝ)*(sp12) + (745816014755741/25000000000000 : ℝ)*(sp13) + (596658262571797/20000000000000 : ℝ)*(sp14) + (1108087390435571/100000000000000 : ℝ)*(sp15) + (1108138980062899/100000000000000 : ℝ)*(f.failure) + (745844139961577/25000000000000 : ℝ)*(f.sum) + (1428238325607/3395000000000000000000000000 : ℝ)*base65 + (832946896985734289/679000000000000000000000000000000 : ℝ)*base67 + (137874197678734289/679000000000000000000000000000000 : ℝ)*base69 + (6853826856919734289/679000000000000000000000000000000 : ℝ)*base71 + (14531722842943/3395000000000000000000000000 : ℝ)*base74 + (5675862544471734289/679000000000000000000000000000000 : ℝ)*base75 + (6034149474304734289/679000000000000000000000000000000 : ℝ)*base77 + (8343647058663734289/679000000000000000000000000000000 : ℝ)*base79 + (20706911037/212187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (83659811/10000000000000000000000 : ℝ)*base90 + (83659811/10000000000000000000000 : ℝ)*base92 + (83659811/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1674_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65173/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14721/25000 : ℝ) else (40811/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88453/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1674_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1674_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65173/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14721/25000 : ℝ) else (40811/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88453/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1674_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1674_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1674_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5011/1024 : ℝ) ≤ p) (hpb : p ≤ (5015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183281711/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65173/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14721/25000 : ℝ) else (40811/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88453/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1674_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
