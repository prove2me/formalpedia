-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1697_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:43:47.154632+00:00
-- url     : https://prove2.me/submissions/dedb0083-80a4-4fce-8cd2-3ce847650b6f

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
theorem support_rectangle_w1697_s0_0 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-343939333/2500000000 : ℝ)*x 0 + (5724629501/10000000000 : ℝ)*x 1 + (2472978577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343939333/2500000000 : ℝ)^5199 ≤ (4228851753007/50000000000000 : ℝ)^4175 := by
    have hnat : (343939333 : ℕ)^5199*50000000000000^4175 ≤ 4228851753007^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343939333 2500000000 4228851753007 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5724629501/10000000000 : ℝ)^5199 ≤ (3120399740821/6250000000000 : ℝ)^4175 := by
    have hnat : (5724629501 : ℕ)^5199*6250000000000^4175 ≤ 3120399740821^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724629501 10000000000 3120399740821 6250000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2472978577/5000000000 : ℝ)^5199 ≤ (41615900634563/100000000000000 : ℝ)^4175 := by
    have hnat : (2472978577 : ℕ)^5199*100000000000000^4175 ≤ 41615900634563^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472978577 5000000000 41615900634563 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343939333/2500000000 : ℝ), (5724629501/10000000000 : ℝ), (2472978577/5000000000 : ℝ)] ![(4228851753007/50000000000000 : ℝ), (3120399740821/6250000000000 : ℝ), (41615900634563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343939333/2500000000 : ℝ)|^5199 ≤ (4228851753007/50000000000000 : ℝ)^4175
        have hw : |(-343939333/2500000000 : ℝ)|=(343939333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5724629501/10000000000 : ℝ)|^5199 ≤ (3120399740821/6250000000000 : ℝ)^4175
        have hw : |(5724629501/10000000000 : ℝ)|=(5724629501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2472978577/5000000000 : ℝ)|^5199 ≤ (41615900634563/100000000000000 : ℝ)^4175
        have hw : |(2472978577/5000000000 : ℝ)|=(2472978577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s0_1 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706752933/5000000000 : ℝ)*x 0 + (-899626627/5000000000 : ℝ)*x 1 + (1236489503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706752933/5000000000 : ℝ)^5199 ≤ (9314060403783/20000000000000 : ℝ)^4175 := by
    have hnat : (2706752933 : ℕ)^5199*20000000000000^4175 ≤ 9314060403783^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706752933 5000000000 9314060403783 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899626627/5000000000 : ℝ)^5199 ≤ (11813788347009/100000000000000 : ℝ)^4175 := by
    have hnat : (899626627 : ℕ)^5199*100000000000000^4175 ≤ 11813788347009^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899626627 5000000000 11813788347009 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236489503/2500000000 : ℝ)^5199 ≤ (41615909624561/100000000000000 : ℝ)^4175 := by
    have hnat : (1236489503 : ℕ)^5199*100000000000000^4175 ≤ 41615909624561^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236489503 2500000000 41615909624561 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706752933/5000000000 : ℝ), (-899626627/5000000000 : ℝ), (1236489503/2500000000 : ℝ)] ![(9314060403783/20000000000000 : ℝ), (11813788347009/100000000000000 : ℝ), (41615909624561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706752933/5000000000 : ℝ)|^5199 ≤ (9314060403783/20000000000000 : ℝ)^4175
        have hw : |(2706752933/5000000000 : ℝ)|=(2706752933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-899626627/5000000000 : ℝ)|^5199 ≤ (11813788347009/100000000000000 : ℝ)^4175
        have hw : |(-899626627/5000000000 : ℝ)|=(899626627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1236489503/2500000000 : ℝ)|^5199 ≤ (41615909624561/100000000000000 : ℝ)^4175
        have hw : |(1236489503/2500000000 : ℝ)|=(1236489503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s0_2 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5413508523/10000000000 : ℝ)*x 0 + (4945957331/10000000000 : ℝ)*x 1 + (-899625323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413508523/10000000000 : ℝ)^5199 ≤ (23285165241111/50000000000000 : ℝ)^4175 := by
    have hnat : (5413508523 : ℕ)^5199*50000000000000^4175 ≤ 23285165241111^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413508523 10000000000 23285165241111 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4945957331/10000000000 : ℝ)^5199 ≤ (41615902489143/100000000000000 : ℝ)^4175 := by
    have hnat : (4945957331 : ℕ)^5199*100000000000000^4175 ≤ 41615902489143^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4945957331 10000000000 41615902489143 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899625323/5000000000 : ℝ)^5199 ≤ (2362753404611/20000000000000 : ℝ)^4175 := by
    have hnat : (899625323 : ℕ)^5199*20000000000000^4175 ≤ 2362753404611^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899625323 5000000000 2362753404611 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413508523/10000000000 : ℝ), (4945957331/10000000000 : ℝ), (-899625323/5000000000 : ℝ)] ![(23285165241111/50000000000000 : ℝ), (41615902489143/100000000000000 : ℝ), (2362753404611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413508523/10000000000 : ℝ)|^5199 ≤ (23285165241111/50000000000000 : ℝ)^4175
        have hw : |(5413508523/10000000000 : ℝ)|=(5413508523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4945957331/10000000000 : ℝ)|^5199 ≤ (41615902489143/100000000000000 : ℝ)^4175
        have hw : |(4945957331/10000000000 : ℝ)|=(4945957331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-899625323/5000000000 : ℝ)|^5199 ≤ (2362753404611/20000000000000 : ℝ)^4175
        have hw : |(-899625323/5000000000 : ℝ)|=(899625323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s0_3 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (202529611/500000000 : ℝ)*x 0 + (5959643/19531250 : ℝ)*x 1 + (1310515407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202529611/500000000 : ℝ)^5199 ≤ (32452996592623/100000000000000 : ℝ)^4175 := by
    have hnat : (202529611 : ℕ)^5199*100000000000000^4175 ≤ 32452996592623^4175*500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202529611 500000000 32452996592623 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5959643/19531250 : ℝ)^5199 ≤ (22806119553203/100000000000000 : ℝ)^4175 := by
    have hnat : (5959643 : ℕ)^5199*100000000000000^4175 ≤ 22806119553203^4175*19531250^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959643 19531250 22806119553203 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310515407/2500000000 : ℝ)^5199 ≤ (5592610479361/12500000000000 : ℝ)^4175 := by
    have hnat : (1310515407 : ℕ)^5199*12500000000000^4175 ≤ 5592610479361^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310515407 2500000000 5592610479361 12500000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(202529611/500000000 : ℝ), (5959643/19531250 : ℝ), (1310515407/2500000000 : ℝ)] ![(32452996592623/100000000000000 : ℝ), (22806119553203/100000000000000 : ℝ), (5592610479361/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(202529611/500000000 : ℝ)|^5199 ≤ (32452996592623/100000000000000 : ℝ)^4175
        have hw : |(202529611/500000000 : ℝ)|=(202529611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5959643/19531250 : ℝ)|^5199 ≤ (22806119553203/100000000000000 : ℝ)^4175
        have hw : |(5959643/19531250 : ℝ)|=(5959643/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310515407/2500000000 : ℝ)|^5199 ≤ (5592610479361/12500000000000 : ℝ)^4175
        have hw : |(1310515407/2500000000 : ℝ)|=(1310515407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s0_4 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-344410331/2500000000 : ℝ)*x 0 + (2482680573/5000000000 : ℝ)*x 1 + (570456313/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344410331/2500000000 : ℝ)^5199 ≤ (8472128841291/100000000000000 : ℝ)^4175 := by
    have hnat : (344410331 : ℕ)^5199*100000000000000^4175 ≤ 8472128841291^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344410331 2500000000 8472128841291 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482680573/5000000000 : ℝ)^5199 ≤ (20909655262227/50000000000000 : ℝ)^4175 := by
    have hnat : (2482680573 : ℕ)^5199*50000000000000^4175 ≤ 20909655262227^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482680573 5000000000 20909655262227 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570456313/1000000000 : ℝ)^5199 ≤ (12427140156569/25000000000000 : ℝ)^4175 := by
    have hnat : (570456313 : ℕ)^5199*25000000000000^4175 ≤ 12427140156569^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570456313 1000000000 12427140156569 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-344410331/2500000000 : ℝ), (2482680573/5000000000 : ℝ), (570456313/1000000000 : ℝ)] ![(8472128841291/100000000000000 : ℝ), (20909655262227/50000000000000 : ℝ), (12427140156569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-344410331/2500000000 : ℝ)|^5199 ≤ (8472128841291/100000000000000 : ℝ)^4175
        have hw : |(-344410331/2500000000 : ℝ)|=(344410331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2482680573/5000000000 : ℝ)|^5199 ≤ (20909655262227/50000000000000 : ℝ)^4175
        have hw : |(2482680573/5000000000 : ℝ)|=(2482680573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570456313/1000000000 : ℝ)|^5199 ≤ (12427140156569/25000000000000 : ℝ)^4175
        have hw : |(570456313/1000000000 : ℝ)|=(570456313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s0_5 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202166761/10000000000 : ℝ)*x 0 + (-1040646821/10000000000 : ℝ)*x 1 + (22818253/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202166761/10000000000 : ℝ)^5199 ≤ (22158631899063/50000000000000 : ℝ)^4175 := by
    have hnat : (5202166761 : ℕ)^5199*50000000000000^4175 ≤ 22158631899063^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202166761 10000000000 22158631899063 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040646821/10000000000 : ℝ)^5199 ≤ (5974174269517/100000000000000 : ℝ)^4175 := by
    have hnat : (1040646821 : ℕ)^5199*100000000000000^4175 ≤ 5974174269517^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040646821 10000000000 5974174269517 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22818253/40000000 : ℝ)^5199 ≤ (49708561928403/100000000000000 : ℝ)^4175 := by
    have hnat : (22818253 : ℕ)^5199*100000000000000^4175 ≤ 49708561928403^4175*40000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22818253 40000000 49708561928403 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202166761/10000000000 : ℝ), (-1040646821/10000000000 : ℝ), (22818253/40000000 : ℝ)] ![(22158631899063/50000000000000 : ℝ), (5974174269517/100000000000000 : ℝ), (49708561928403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202166761/10000000000 : ℝ)|^5199 ≤ (22158631899063/50000000000000 : ℝ)^4175
        have hw : |(5202166761/10000000000 : ℝ)|=(5202166761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040646821/10000000000 : ℝ)|^5199 ≤ (5974174269517/100000000000000 : ℝ)^4175
        have hw : |(-1040646821/10000000000 : ℝ)|=(1040646821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22818253/40000000 : ℝ)|^5199 ≤ (49708561928403/100000000000000 : ℝ)^4175
        have hw : |(22818253/40000000 : ℝ)|=(22818253/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s0_6 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2601083349/5000000000 : ℝ)*x 0 + (5704563731/10000000000 : ℝ)*x 1 + (-1040646183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2601083349/5000000000 : ℝ)^5199 ≤ (44317263129793/100000000000000 : ℝ)^4175 := by
    have hnat : (2601083349 : ℕ)^5199*100000000000000^4175 ≤ 44317263129793^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601083349 5000000000 44317263129793 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704563731/10000000000 : ℝ)^5199 ≤ (49708567147763/100000000000000 : ℝ)^4175 := by
    have hnat : (5704563731 : ℕ)^5199*100000000000000^4175 ≤ 49708567147763^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704563731 10000000000 49708567147763 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040646183/10000000000 : ℝ)^5199 ≤ (2987084854267/50000000000000 : ℝ)^4175 := by
    have hnat : (1040646183 : ℕ)^5199*50000000000000^4175 ≤ 2987084854267^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040646183 10000000000 2987084854267 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2601083349/5000000000 : ℝ), (5704563731/10000000000 : ℝ), (-1040646183/10000000000 : ℝ)] ![(44317263129793/100000000000000 : ℝ), (49708567147763/100000000000000 : ℝ), (2987084854267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2601083349/5000000000 : ℝ)|^5199 ≤ (44317263129793/100000000000000 : ℝ)^4175
        have hw : |(2601083349/5000000000 : ℝ)|=(2601083349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5704563731/10000000000 : ℝ)|^5199 ≤ (49708567147763/100000000000000 : ℝ)^4175
        have hw : |(5704563731/10000000000 : ℝ)|=(5704563731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040646183/10000000000 : ℝ)|^5199 ≤ (2987084854267/50000000000000 : ℝ)^4175
        have hw : |(-1040646183/10000000000 : ℝ)|=(1040646183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s0_7 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2027946411/5000000000 : ℝ)*x 0 + (518746691/1000000000 : ℝ)*x 1 + (3107790587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027946411/5000000000 : ℝ)^5199 ≤ (16252944569809/50000000000000 : ℝ)^4175 := by
    have hnat : (2027946411 : ℕ)^5199*50000000000000^4175 ≤ 16252944569809^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027946411 5000000000 16252944569809 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518746691/1000000000 : ℝ)^5199 ≤ (44161375215137/100000000000000 : ℝ)^4175 := by
    have hnat : (518746691 : ℕ)^5199*100000000000000^4175 ≤ 44161375215137^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518746691 1000000000 44161375215137 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3107790587/10000000000 : ℝ)^5199 ≤ (23332735636497/100000000000000 : ℝ)^4175 := by
    have hnat : (3107790587 : ℕ)^5199*100000000000000^4175 ≤ 23332735636497^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107790587 10000000000 23332735636497 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2027946411/5000000000 : ℝ), (518746691/1000000000 : ℝ), (3107790587/10000000000 : ℝ)] ![(16252944569809/50000000000000 : ℝ), (44161375215137/100000000000000 : ℝ), (23332735636497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2027946411/5000000000 : ℝ)|^5199 ≤ (16252944569809/50000000000000 : ℝ)^4175
        have hw : |(2027946411/5000000000 : ℝ)|=(2027946411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518746691/1000000000 : ℝ)|^5199 ≤ (44161375215137/100000000000000 : ℝ)^4175
        have hw : |(518746691/1000000000 : ℝ)|=(518746691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3107790587/10000000000 : ℝ)|^5199 ≤ (23332735636497/100000000000000 : ℝ)^4175
        have hw : |(3107790587/10000000000 : ℝ)|=(3107790587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1697_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5657/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22377/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5191/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5191 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5191*1^1024 ≤ 0^1024*1^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5191/1024 : ℝ) ≤ (480483432507294019/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5191 ≤ (480483432507294019/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5191*50000000000000000000^1024 ≤ 480483432507294019^1024*5^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 480483432507294019 50000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (480483432507294019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5191 := by
      have hnat : (1 : ℕ)^1024*1^5191 ≤ 1^5191*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50480483432507294019/50000000000000000000 : ℝ) ≤ (500944188427309/500000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (50480483432507294019/50000000000000000000 : ℝ)^1024 ≤ (500944188427309/500000000000000 : ℝ)^5191 := by
      have hnat : (50480483432507294019 : ℕ)^1024*500000000000000^5191 ≤ 500944188427309^5191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50480483432507294019 50000000000000000000 500944188427309 500000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500944188427309/500000000000000 : ℝ)) (X := (50480483432507294019/50000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25480483432507294019/25000000000000000000 : ℝ) ≤ (250944188427309/250000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (25480483432507294019/25000000000000000000 : ℝ)^1024 ≤ (250944188427309/250000000000000 : ℝ)^5191 := by
      have hnat : (25480483432507294019 : ℕ)^1024*250000000000000^5191 ≤ 250944188427309^5191*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25480483432507294019 25000000000000000000 250944188427309 250000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250944188427309/250000000000000 : ℝ)) (X := (25480483432507294019/25000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(944188427309/200000000000000 : ℝ)*(0 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(944188427309/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(480483432507294019/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(944188427309/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5191/1024 : ℝ) := by
    rw [show (1 : ℝ)+(944188427309/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(500944188427309/500000000000000 : ℝ) by norm_num, show 1+(480483432507294019/50000000000000000000 : ℝ)+(0 : ℝ)=(50480483432507294019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(480483432507294019/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(944188427309/200000000000000 : ℝ)*(2/5 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(944188427309/200000000000000 : ℝ)*(2/5 : ℝ)=(250944188427309/250000000000000 : ℝ) by norm_num, show 1+2*(480483432507294019/50000000000000000000 : ℝ)=(25480483432507294019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(944188427309/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (944188427309/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(944188427309/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (944188427309/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(944188427309/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (944188427309/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-343939333/2500000000 : ℝ)*X 0 0+(5724629501/10000000000 : ℝ)*X 0 1+(2472978577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706752933/5000000000 : ℝ)*X 1 0+(-899626627/5000000000 : ℝ)*X 1 1+(1236489503/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5413508523/10000000000 : ℝ)*X 2 0+(4945957331/10000000000 : ℝ)*X 2 1+(-899625323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((202529611/500000000 : ℝ)*X 0 0+(5959643/19531250 : ℝ)*X 0 1+(1310515407/2500000000 : ℝ)*X 0 2+(202529611/500000000 : ℝ)*X 1 0+(5959643/19531250 : ℝ)*X 1 1+(1310515407/2500000000 : ℝ)*X 1 2+(202529611/500000000 : ℝ)*X 2 0+(5959643/19531250 : ℝ)*X 2 1+(1310515407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-344410331/2500000000 : ℝ)*X 0 0+(2482680573/5000000000 : ℝ)*X 0 1+(570456313/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5202166761/10000000000 : ℝ)*X 1 0+(-1040646821/10000000000 : ℝ)*X 1 1+(22818253/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2601083349/5000000000 : ℝ)*X 2 0+(5704563731/10000000000 : ℝ)*X 2 1+(-1040646183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2027946411/5000000000 : ℝ)*X 0 0+(518746691/1000000000 : ℝ)*X 0 1+(3107790587/10000000000 : ℝ)*X 0 2+(2027946411/5000000000 : ℝ)*X 1 0+(518746691/1000000000 : ℝ)*X 1 1+(3107790587/10000000000 : ℝ)*X 1 2+(2027946411/5000000000 : ℝ)*X 2 0+(518746691/1000000000 : ℝ)*X 2 1+(3107790587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7277962297641629376363/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (324769991/50000000000000 : ℝ)*(base19) + (957322461/100000000000000 : ℝ)*(base23) + (5842821/2000000000000 : ℝ)*(base24) + (4113703/25000000000000 : ℝ)*(upper4) + (67432541/50000000000000 : ℝ)*(upper5) + (435179907908231/50000000000000 : ℝ)*(major0) + (435179907908231/50000000000000 : ℝ)*(major1) + (435179907908231/50000000000000 : ℝ)*(major2) + (8026499879821/625000000000 : ℝ)*(sp0) + (256849022231159/20000000000000 : ℝ)*(sp1) + (642122255616133/50000000000000 : ℝ)*(sp2) + (18258870397763/4000000000000 : ℝ)*(sp3) + (5779924417/100000000000000 : ℝ)*(sp4) + (958457037/50000000000000 : ℝ)*(sp7) + (456473676858149/100000000000000 : ℝ)*(f.failure) + (1284245760695777/100000000000000 : ℝ)*(f.sum) + (13249517780379/5000000000000000000000000000 : ℝ)*base65 + (53130988460379/10000000000000000000000000000 : ℝ)*base67 + (12757515599621/10000000000000000000000000000 : ℝ)*base70 + (55781118300379/10000000000000000000000000000 : ℝ)*base71 + (15780888230379/5000000000000000000000000000 : ℝ)*base73 + (23009764499621/10000000000000000000000000000 : ℝ)*base76 + (26269021820379/10000000000000000000000000000 : ℝ)*base77 + (46270500420379/10000000000000000000000000000 : ℝ)*base79 + (1120127770379/5000000000000000000000000000 : ℝ)*base81 + (12420469/10000000000000000000000 : ℝ)*base90 + (12420469/10000000000000000000000 : ℝ)*base92 + (12420469/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47567205852317261690763/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2288890951/100000000000000 : ℝ)*(base19) + (2326663459/100000000000000 : ℝ)*(base23) + (3120929/20000000000000 : ℝ)*(base32) + (24040407/6250000000000 : ℝ)*(upper3) + (333483267/100000000000000 : ℝ)*(upper5) + (458413576533823/50000000000000 : ℝ)*(major0) + (458413576533823/50000000000000 : ℝ)*(major1) + (458413576533823/50000000000000 : ℝ)*(major2) + (4051948269/50000000000000 : ℝ)*(sp1) + (4718412929/50000000000000 : ℝ)*(sp2) + (676404898959161/50000000000000 : ℝ)*(sp4) + (1352799405130833/100000000000000 : ℝ)*(sp5) + (338199508607251/25000000000000 : ℝ)*(sp6) + (240422087748807/50000000000000 : ℝ)*(sp7) + (480844191102259/100000000000000 : ℝ)*(f.failure) + (676404898959161/50000000000000 : ℝ)*(f.sum) + (7561873472307/5000000000000000000000000000 : ℝ)*base65 + (87246882147693/10000000000000000000000000000 : ℝ)*base68 + (68382457407693/10000000000000000000000000000 : ℝ)*base70 + (26850789917693/10000000000000000000000000000 : ℝ)*base72 + (20167115602693/5000000000000000000000000000 : ℝ)*base74 + (83194275867693/10000000000000000000000000000 : ℝ)*base76 + (11199583032307/10000000000000000000000000000 : ℝ)*base77 + (2426901247693/10000000000000000000000000000 : ℝ)*base80 + (5939501717693/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (85150621/10000000000000000000000 : ℝ)*base89 + (85150621/10000000000000000000000 : ℝ)*base91 + (85150621/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1697_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22377/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1697_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1697_s1_0 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-727823939/5000000000 : ℝ)*x 0 + (2748970061/5000000000 : ℝ)*x 1 + (5120243219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (727823939/5000000000 : ℝ)^5199 ≤ (9073599564903/100000000000000 : ℝ)^4175 := by
    have hnat : (727823939 : ℕ)^5199*100000000000000^4175 ≤ 9073599564903^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727823939 5000000000 9073599564903 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748970061/5000000000 : ℝ)^5199 ≤ (370910417637/781250000000 : ℝ)^4175 := by
    have hnat : (2748970061 : ℕ)^5199*781250000000^4175 ≤ 370910417637^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748970061 5000000000 370910417637 781250000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5120243219/10000000000 : ℝ)^5199 ≤ (4344986696187/10000000000000 : ℝ)^4175 := by
    have hnat : (5120243219 : ℕ)^5199*10000000000000^4175 ≤ 4344986696187^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120243219 10000000000 4344986696187 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-727823939/5000000000 : ℝ), (2748970061/5000000000 : ℝ), (5120243219/10000000000 : ℝ)] ![(9073599564903/100000000000000 : ℝ), (370910417637/781250000000 : ℝ), (4344986696187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-727823939/5000000000 : ℝ)|^5199 ≤ (9073599564903/100000000000000 : ℝ)^4175
        have hw : |(-727823939/5000000000 : ℝ)|=(727823939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748970061/5000000000 : ℝ)|^5199 ≤ (370910417637/781250000000 : ℝ)^4175
        have hw : |(2748970061/5000000000 : ℝ)|=(2748970061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5120243219/10000000000 : ℝ)|^5199 ≤ (4344986696187/10000000000000 : ℝ)^4175
        have hw : |(5120243219/10000000000 : ℝ)|=(5120243219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s1_1 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353116541/10000000000 : ℝ)*x 0 + (-1652467077/10000000000 : ℝ)*x 1 + (1280060669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353116541/10000000000 : ℝ)^5199 ≤ (9184852899/20000000000 : ℝ)^4175 := by
    have hnat : (5353116541 : ℕ)^5199*20000000000^4175 ≤ 9184852899^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353116541 10000000000 9184852899 20000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1652467077/10000000000 : ℝ)^5199 ≤ (2656468566001/25000000000000 : ℝ)^4175 := by
    have hnat : (1652467077 : ℕ)^5199*25000000000000^4175 ≤ 2656468566001^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652467077 10000000000 2656468566001 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280060669/2500000000 : ℝ)^5199 ≤ (43449861223863/100000000000000 : ℝ)^4175 := by
    have hnat : (1280060669 : ℕ)^5199*100000000000000^4175 ≤ 43449861223863^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280060669 2500000000 43449861223863 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353116541/10000000000 : ℝ), (-1652467077/10000000000 : ℝ), (1280060669/2500000000 : ℝ)] ![(9184852899/20000000000 : ℝ), (2656468566001/25000000000000 : ℝ), (43449861223863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353116541/10000000000 : ℝ)|^5199 ≤ (9184852899/20000000000 : ℝ)^4175
        have hw : |(5353116541/10000000000 : ℝ)|=(5353116541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1652467077/10000000000 : ℝ)|^5199 ≤ (2656468566001/25000000000000 : ℝ)^4175
        have hw : |(-1652467077/10000000000 : ℝ)|=(1652467077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1280060669/2500000000 : ℝ)|^5199 ≤ (43449861223863/100000000000000 : ℝ)^4175
        have hw : |(1280060669/2500000000 : ℝ)|=(1280060669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s1_2 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676557729/5000000000 : ℝ)*x 0 + (160007613/312500000 : ℝ)*x 1 + (-1652467281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676557729/5000000000 : ℝ)^5199 ≤ (22962126462581/50000000000000 : ℝ)^4175 := by
    have hnat : (2676557729 : ℕ)^5199*50000000000000^4175 ≤ 22962126462581^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676557729 5000000000 22962126462581 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160007613/312500000 : ℝ)^5199 ≤ (2172493557853/5000000000000 : ℝ)^4175 := by
    have hnat : (160007613 : ℕ)^5199*5000000000000^4175 ≤ 2172493557853^4175*312500000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160007613 312500000 2172493557853 5000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1652467281/10000000000 : ℝ)^5199 ≤ (10625875897527/100000000000000 : ℝ)^4175 := by
    have hnat : (1652467281 : ℕ)^5199*100000000000000^4175 ≤ 10625875897527^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652467281 10000000000 10625875897527 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676557729/5000000000 : ℝ), (160007613/312500000 : ℝ), (-1652467281/10000000000 : ℝ)] ![(22962126462581/50000000000000 : ℝ), (2172493557853/5000000000000 : ℝ), (10625875897527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676557729/5000000000 : ℝ)|^5199 ≤ (22962126462581/50000000000000 : ℝ)^4175
        have hw : |(2676557729/5000000000 : ℝ)|=(2676557729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160007613/312500000 : ℝ)|^5199 ≤ (2172493557853/5000000000000 : ℝ)^4175
        have hw : |(160007613/312500000 : ℝ)|=(160007613/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1652467281/10000000000 : ℝ)|^5199 ≤ (10625875897527/100000000000000 : ℝ)^4175
        have hw : |(-1652467281/10000000000 : ℝ)|=(1652467281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s1_3 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2059028199/5000000000 : ℝ)*x 0 + (3609174479/10000000000 : ℝ)*x 1 + (467178923/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059028199/5000000000 : ℝ)^5199 ≤ (33127455232801/100000000000000 : ℝ)^4175 := by
    have hnat : (2059028199 : ℕ)^5199*100000000000000^4175 ≤ 33127455232801^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059028199 5000000000 33127455232801 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3609174479/10000000000 : ℝ)^5199 ≤ (1124381102431/4000000000000 : ℝ)^4175 := by
    have hnat : (3609174479 : ℕ)^5199*4000000000000^4175 ≤ 1124381102431^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3609174479 10000000000 1124381102431 4000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467178923/1000000000 : ℝ)^5199 ≤ (19381508596149/50000000000000 : ℝ)^4175 := by
    have hnat : (467178923 : ℕ)^5199*50000000000000^4175 ≤ 19381508596149^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467178923 1000000000 19381508596149 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2059028199/5000000000 : ℝ), (3609174479/10000000000 : ℝ), (467178923/1000000000 : ℝ)] ![(33127455232801/100000000000000 : ℝ), (1124381102431/4000000000000 : ℝ), (19381508596149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2059028199/5000000000 : ℝ)|^5199 ≤ (33127455232801/100000000000000 : ℝ)^4175
        have hw : |(2059028199/5000000000 : ℝ)|=(2059028199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3609174479/10000000000 : ℝ)|^5199 ≤ (1124381102431/4000000000000 : ℝ)^4175
        have hw : |(3609174479/10000000000 : ℝ)|=(3609174479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467178923/1000000000 : ℝ)|^5199 ≤ (19381508596149/50000000000000 : ℝ)^4175
        have hw : |(467178923/1000000000 : ℝ)|=(467178923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s1_4 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-90991291/625000000 : ℝ)*x 0 + (5124805987/10000000000 : ℝ)*x 1 + (2746650873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90991291/625000000 : ℝ)^5199 ≤ (1815050245339/20000000000000 : ℝ)^4175 := by
    have hnat : (90991291 : ℕ)^5199*20000000000000^4175 ≤ 1815050245339^4175*625000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90991291 625000000 1815050245339 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124805987/10000000000 : ℝ)^5199 ≤ (10874522013223/25000000000000 : ℝ)^4175 := by
    have hnat : (5124805987 : ℕ)^5199*25000000000000^4175 ≤ 10874522013223^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124805987 10000000000 10874522013223 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746650873/5000000000 : ℝ)^5199 ≤ (379413285639/800000000000 : ℝ)^4175 := by
    have hnat : (2746650873 : ℕ)^5199*800000000000^4175 ≤ 379413285639^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746650873 5000000000 379413285639 800000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90991291/625000000 : ℝ), (5124805987/10000000000 : ℝ), (2746650873/5000000000 : ℝ)] ![(1815050245339/20000000000000 : ℝ), (10874522013223/25000000000000 : ℝ), (379413285639/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90991291/625000000 : ℝ)|^5199 ≤ (1815050245339/20000000000000 : ℝ)^4175
        have hw : |(-90991291/625000000 : ℝ)|=(90991291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124805987/10000000000 : ℝ)|^5199 ≤ (10874522013223/25000000000000 : ℝ)^4175
        have hw : |(5124805987/10000000000 : ℝ)|=(5124805987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746650873/5000000000 : ℝ)|^5199 ≤ (379413285639/800000000000 : ℝ)^4175
        have hw : |(2746650873/5000000000 : ℝ)|=(2746650873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s1_5 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626011911/5000000000 : ℝ)*x 0 + (-127940797/1000000000 : ℝ)*x 1 + (686662703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626011911/5000000000 : ℝ)^5199 ≤ (44846790166533/100000000000000 : ℝ)^4175 := by
    have hnat : (2626011911 : ℕ)^5199*100000000000000^4175 ≤ 44846790166533^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626011911 5000000000 44846790166533 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127940797/1000000000 : ℝ)^5199 ≤ (7726550424181/100000000000000 : ℝ)^4175 := by
    have hnat : (127940797 : ℕ)^5199*100000000000000^4175 ≤ 7726550424181^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127940797 1000000000 7726550424181 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686662703/1250000000 : ℝ)^5199 ≤ (23713329696621/50000000000000 : ℝ)^4175 := by
    have hnat : (686662703 : ℕ)^5199*50000000000000^4175 ≤ 23713329696621^4175*1250000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686662703 1250000000 23713329696621 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626011911/5000000000 : ℝ), (-127940797/1000000000 : ℝ), (686662703/1250000000 : ℝ)] ![(44846790166533/100000000000000 : ℝ), (7726550424181/100000000000000 : ℝ), (23713329696621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626011911/5000000000 : ℝ)|^5199 ≤ (44846790166533/100000000000000 : ℝ)^4175
        have hw : |(2626011911/5000000000 : ℝ)|=(2626011911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127940797/1000000000 : ℝ)|^5199 ≤ (7726550424181/100000000000000 : ℝ)^4175
        have hw : |(-127940797/1000000000 : ℝ)|=(127940797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686662703/1250000000 : ℝ)|^5199 ≤ (23713329696621/50000000000000 : ℝ)^4175
        have hw : |(686662703/1250000000 : ℝ)|=(686662703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s1_6 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328251477/625000000 : ℝ)*x 0 + (2746650883/5000000000 : ℝ)*x 1 + (-319852009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328251477/625000000 : ℝ)^5199 ≤ (22423394073103/50000000000000 : ℝ)^4175 := by
    have hnat : (328251477 : ℕ)^5199*50000000000000^4175 ≤ 22423394073103^4175*625000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328251477 625000000 22423394073103 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746650883/5000000000 : ℝ)^5199 ≤ (47426660919897/100000000000000 : ℝ)^4175 := by
    have hnat : (2746650883 : ℕ)^5199*100000000000000^4175 ≤ 47426660919897^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746650883 5000000000 47426660919897 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319852009/2500000000 : ℝ)^5199 ≤ (7726550920527/100000000000000 : ℝ)^4175 := by
    have hnat : (319852009 : ℕ)^5199*100000000000000^4175 ≤ 7726550920527^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319852009 2500000000 7726550920527 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328251477/625000000 : ℝ), (2746650883/5000000000 : ℝ), (-319852009/2500000000 : ℝ)] ![(22423394073103/50000000000000 : ℝ), (47426660919897/100000000000000 : ℝ), (7726550920527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328251477/625000000 : ℝ)|^5199 ≤ (22423394073103/50000000000000 : ℝ)^4175
        have hw : |(328251477/625000000 : ℝ)|=(328251477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746650883/5000000000 : ℝ)|^5199 ≤ (47426660919897/100000000000000 : ℝ)^4175
        have hw : |(2746650883/5000000000 : ℝ)|=(2746650883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319852009/2500000000 : ℝ)|^5199 ≤ (7726550920527/100000000000000 : ℝ)^4175
        have hw : |(-319852009/2500000000 : ℝ)|=(319852009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s1_7 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4118654221/10000000000 : ℝ)*x 0 + (2329475879/5000000000 : ℝ)*x 1 + (1811111441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4118654221/10000000000 : ℝ)^5199 ≤ (16566722014087/50000000000000 : ℝ)^4175 := by
    have hnat : (4118654221 : ℕ)^5199*50000000000000^4175 ≤ 16566722014087^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118654221 10000000000 16566722014087 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2329475879/5000000000 : ℝ)^5199 ≤ (38630421106741/100000000000000 : ℝ)^4175 := by
    have hnat : (2329475879 : ℕ)^5199*100000000000000^4175 ≤ 38630421106741^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329475879 5000000000 38630421106741 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1811111441/5000000000 : ℝ)^5199 ≤ (28236134847579/100000000000000 : ℝ)^4175 := by
    have hnat : (1811111441 : ℕ)^5199*100000000000000^4175 ≤ 28236134847579^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811111441 5000000000 28236134847579 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4118654221/10000000000 : ℝ), (2329475879/5000000000 : ℝ), (1811111441/5000000000 : ℝ)] ![(16566722014087/50000000000000 : ℝ), (38630421106741/100000000000000 : ℝ), (28236134847579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4118654221/10000000000 : ℝ)|^5199 ≤ (16566722014087/50000000000000 : ℝ)^4175
        have hw : |(4118654221/10000000000 : ℝ)|=(4118654221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2329475879/5000000000 : ℝ)|^5199 ≤ (38630421106741/100000000000000 : ℝ)^4175
        have hw : |(2329475879/5000000000 : ℝ)|=(2329475879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1811111441/5000000000 : ℝ)|^5199 ≤ (28236134847579/100000000000000 : ℝ)^4175
        have hw : |(1811111441/5000000000 : ℝ)|=(1811111441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1697_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22377/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1909/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17593/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22377/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5657/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22377/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5657/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22377/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5657/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22377/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5657/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22377/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5657/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22377/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5657/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5657/100000 : ℝ) ^ (5191/1024 : ℝ) ≤ (2967018841957/6250000000000000000 : ℝ) := by
    have hpowers : (5657/100000 : ℝ)^5191 ≤ (2967018841957/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5657 : ℕ)^5191*6250000000000000000^1024 ≤ 2967018841957^1024*100000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5657 100000 2967018841957 6250000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5657/100000 : ℝ)) (X := (2967018841957/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22377/100000 : ℝ) ^ (5191/1024 : ℝ) ≤ (50573989248049063/100000000000000000000 : ℝ) := by
    have hpowers : (22377/100000 : ℝ)^5191 ≤ (50573989248049063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22377 : ℕ)^5191*100000000000000000000^1024 ≤ 50573989248049063^1024*100000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22377 100000 50573989248049063 100000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22377/100000 : ℝ)) (X := (50573989248049063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125002967018841957/3125000000000000000 : ℝ) ≤ (5000000936459607/5000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (3125002967018841957/3125000000000000000 : ℝ)^1024 ≤ (5000000936459607/5000000000000000 : ℝ)^5191 := by
      have hnat : (3125002967018841957 : ℕ)^1024*5000000000000000^5191 ≤ 5000000936459607^5191*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125002967018841957 3125000000000000000 5000000936459607 5000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000936459607/5000000000000000 : ℝ)) (X := (3125002967018841957/3125000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (800404971692396163/800000000000000000 : ℝ) ≤ (10000998378882807/10000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (800404971692396163/800000000000000000 : ℝ)^1024 ≤ (10000998378882807/10000000000000000 : ℝ)^5191 := by
      have hnat : (800404971692396163 : ℕ)^1024*10000000000000000^5191 ≤ 10000998378882807^5191*800000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800404971692396163 800000000000000000 10000998378882807 10000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000998378882807/10000000000000000 : ℝ)) (X := (800404971692396163/800000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50050573989248049063/50000000000000000000 : ℝ) ≤ (6251246803029/6250000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (50050573989248049063/50000000000000000000 : ℝ)^1024 ≤ (6251246803029/6250000000000 : ℝ)^5191 := by
      have hnat : (50050573989248049063 : ℕ)^1024*6250000000000^5191 ≤ 6251246803029^5191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50050573989248049063 50000000000000000000 6251246803029 6250000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6251246803029/6250000000000 : ℝ)) (X := (50050573989248049063/50000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2967018841957/6250000000000000000 : ℝ) ≤ ((83594378423368583439/83600000000000000000 : ℝ)+2*(996505963593/1672000000000000 : ℝ)*(5657/100000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (83594378423368583439/83600000000000000000 : ℝ)+2*(996505963593/1672000000000000 : ℝ)*(5657/100000 : ℝ)=(5000000936459607/5000000000000000 : ℝ) by norm_num, show 1+2*(2967018841957/6250000000000000000 : ℝ)=(3125002967018841957/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50573989248049063/100000000000000000000 : ℝ)+(2967018841957/6250000000000000000 : ℝ) ≤ ((83594378423368583439/83600000000000000000 : ℝ)+(996505963593/1672000000000000 : ℝ)*((22377/100000 : ℝ)+(5657/100000 : ℝ)))^(5191/1024 : ℝ) := by
    rw [show (83594378423368583439/83600000000000000000 : ℝ)+(996505963593/1672000000000000 : ℝ)*((22377/100000 : ℝ)+(5657/100000 : ℝ))=(10000998378882807/10000000000000000 : ℝ) by norm_num, show 1+(50573989248049063/100000000000000000000 : ℝ)+(2967018841957/6250000000000000000 : ℝ)=(800404971692396163/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50573989248049063/100000000000000000000 : ℝ) ≤ ((83594378423368583439/83600000000000000000 : ℝ)+2*(996505963593/1672000000000000 : ℝ)*(22377/100000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (83594378423368583439/83600000000000000000 : ℝ)+2*(996505963593/1672000000000000 : ℝ)*(22377/100000 : ℝ)=(6251246803029/6250000000000 : ℝ) by norm_num, show 1+2*(50573989248049063/100000000000000000000 : ℝ)=(50050573989248049063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (83594378423368583439/83600000000000000000 : ℝ)*(X 1 0+X 2 0)+(996505963593/1672000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (5657/100000 : ℝ)) (hi := (22377/100000 : ℝ)) (c := (83594378423368583439/83600000000000000000 : ℝ)) (alpha := (996505963593/1672000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (83594378423368583439/83600000000000000000 : ℝ)*(X 0 1+X 2 1)+(996505963593/1672000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (5657/100000 : ℝ)) (hi := (22377/100000 : ℝ)) (c := (83594378423368583439/83600000000000000000 : ℝ)) (alpha := (996505963593/1672000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (83594378423368583439/83600000000000000000 : ℝ)*(X 0 2+X 1 2)+(996505963593/1672000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (5657/100000 : ℝ)) (hi := (22377/100000 : ℝ)) (c := (83594378423368583439/83600000000000000000 : ℝ)) (alpha := (996505963593/1672000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-727823939/5000000000 : ℝ)*X 0 0+(2748970061/5000000000 : ℝ)*X 0 1+(5120243219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353116541/10000000000 : ℝ)*X 1 0+(-1652467077/10000000000 : ℝ)*X 1 1+(1280060669/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676557729/5000000000 : ℝ)*X 2 0+(160007613/312500000 : ℝ)*X 2 1+(-1652467281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2059028199/5000000000 : ℝ)*X 0 0+(3609174479/10000000000 : ℝ)*X 0 1+(467178923/1000000000 : ℝ)*X 0 2+(2059028199/5000000000 : ℝ)*X 1 0+(3609174479/10000000000 : ℝ)*X 1 1+(467178923/1000000000 : ℝ)*X 1 2+(2059028199/5000000000 : ℝ)*X 2 0+(3609174479/10000000000 : ℝ)*X 2 1+(467178923/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-90991291/625000000 : ℝ)*X 0 0+(5124805987/10000000000 : ℝ)*X 0 1+(2746650873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626011911/5000000000 : ℝ)*X 1 0+(-127940797/1000000000 : ℝ)*X 1 1+(686662703/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328251477/625000000 : ℝ)*X 2 0+(2746650883/5000000000 : ℝ)*X 2 1+(-319852009/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4118654221/10000000000 : ℝ)*X 0 0+(2329475879/5000000000 : ℝ)*X 0 1+(1811111441/5000000000 : ℝ)*X 0 2+(4118654221/10000000000 : ℝ)*X 1 0+(2329475879/5000000000 : ℝ)*X 1 1+(1811111441/5000000000 : ℝ)*X 1 2+(4118654221/10000000000 : ℝ)*X 2 0+(2329475879/5000000000 : ℝ)*X 2 1+(1811111441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4841212709029083995345271447/522500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (257797527/20000000000000 : ℝ)*(base19) + (46147961/6250000000000 : ℝ)*(base23) + (8013739/100000000000000 : ℝ)*(lower2) + (245435291/100000000000000 : ℝ)*(upper3) + (16848463/50000000000000 : ℝ)*(upper5) + (224295304332109/12500000000000 : ℝ)*(major0) + (224295304332109/12500000000000 : ℝ)*(major1) + (224295304332109/12500000000000 : ℝ)*(major2) + (2647636980676509/100000000000000 : ℝ)*(sp0) + (661910529857453/25000000000000 : ℝ)*(sp1) + (264764267005007/10000000000000 : ℝ)*(sp2) + (941077635978537/100000000000000 : ℝ)*(sp3) + (3213870469/50000000000000 : ℝ)*(sp4) + (3516068453/100000000000000 : ℝ)*(sp7) + (94108115204699/10000000000000 : ℝ)*(f.failure) + (2647643408417447/100000000000000 : ℝ)*(f.sum) + (7263119843587/10450000000000000000000000000 : ℝ)*base65 + (11159632944170192851/1045000000000000000000000000000000 : ℝ)*base67 + (372548964659807149/1045000000000000000000000000000000 : ℝ)*base70 + (11771164195820192851/1045000000000000000000000000000000 : ℝ)*base71 + (77166707544787/10450000000000000000000000000 : ℝ)*base73 + (6013601808844807149/1045000000000000000000000000000000 : ℝ)*base76 + (2109865648260192851/1045000000000000000000000000000000 : ℝ)*base77 + (5060528883450192851/1045000000000000000000000000000000 : ℝ)*base79 + (40033778773937/10450000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11371019/1000000000000000000000 : ℝ)*base90 + (11371019/1000000000000000000000 : ℝ)*base92 + (11371019/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82482049632157928352276363/10450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1773102879/100000000000000 : ℝ)*(base19) + (1841162289/100000000000000 : ℝ)*(base23) + (484833/625000000000 : ℝ)*(upper2) + (1935123/781250000000 : ℝ)*(upper3) + (10504237/5000000000000 : ℝ)*(upper5) + (9195765117039/500000000000 : ℝ)*(major0) + (9195765117039/500000000000 : ℝ)*(major1) + (9195765117039/500000000000 : ℝ)*(major2) + (434147787/3125000000000 : ℝ)*(sp1) + (1856949877/12500000000000 : ℝ)*(sp2) + (2713733514127577/100000000000000 : ℝ)*(sp4) + (1356858924147757/50000000000000 : ℝ)*(sp5) + (10600456317837/390625000000 : ℝ)*(sp6) + (964572269587381/100000000000000 : ℝ)*(sp7) + (964572269587381/100000000000000 : ℝ)*(f.failure) + (2713733514127577/100000000000000 : ℝ)*(f.sum) + (6000933929/3344000000000000000000000 : ℝ)*base65 + (173806407086132879/41800000000000000000000000000000 : ℝ)*base68 + (28690692502732879/41800000000000000000000000000000 : ℝ)*base70 + (98713585353067121/41800000000000000000000000000000 : ℝ)*base71 + (802991251773/418000000000000000000000000 : ℝ)*base74 + (125446058643132879/41800000000000000000000000000000 : ℝ)*base76 + (18968553770932879/41800000000000000000000000000000 : ℝ)*base78 + (143915841922332879/41800000000000000000000000000000 : ℝ)*base80 + (96216710791/83600000000000000000000000 : ℝ)*base81 + (66355461/10000000000000000000000 : ℝ)*base90 + (66355461/10000000000000000000000 : ℝ)*base92 + (66355461/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1697_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22377/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1909/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17593/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1697_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1697_s2_0 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1460246793/10000000000 : ℝ)*x 0 + (5479344843/10000000000 : ℝ)*x 1 + (5135772851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1460246793/10000000000 : ℝ)^5199 ≤ (9109311229821/100000000000000 : ℝ)^4175 := by
    have hnat : (1460246793 : ℕ)^5199*100000000000000^4175 ≤ 9109311229821^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460246793 10000000000 9109311229821 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479344843/10000000000 : ℝ)^5199 ≤ (47276655591141/100000000000000 : ℝ)^4175 := by
    have hnat : (5479344843 : ℕ)^5199*100000000000000^4175 ≤ 47276655591141^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479344843 10000000000 47276655591141 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135772851/10000000000 : ℝ)^5199 ≤ (10903508290381/25000000000000 : ℝ)^4175 := by
    have hnat : (5135772851 : ℕ)^5199*25000000000000^4175 ≤ 10903508290381^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135772851 10000000000 10903508290381 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1460246793/10000000000 : ℝ), (5479344843/10000000000 : ℝ), (5135772851/10000000000 : ℝ)] ![(9109311229821/100000000000000 : ℝ), (47276655591141/100000000000000 : ℝ), (10903508290381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1460246793/10000000000 : ℝ)|^5199 ≤ (9109311229821/100000000000000 : ℝ)^4175
        have hw : |(-1460246793/10000000000 : ℝ)|=(1460246793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479344843/10000000000 : ℝ)|^5199 ≤ (47276655591141/100000000000000 : ℝ)^4175
        have hw : |(5479344843/10000000000 : ℝ)|=(5479344843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135772851/10000000000 : ℝ)|^5199 ≤ (10903508290381/25000000000000 : ℝ)^4175
        have hw : |(5135772851/10000000000 : ℝ)|=(5135772851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s2_1 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534811089/1000000000 : ℝ)*x 0 + (-1638628143/10000000000 : ℝ)*x 1 + (5135772733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534811089/1000000000 : ℝ)^5199 ≤ (22935397283553/50000000000000 : ℝ)^4175 := by
    have hnat : (534811089 : ℕ)^5199*50000000000000^4175 ≤ 22935397283553^4175*1000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534811089 1000000000 22935397283553 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1638628143/10000000000 : ℝ)^5199 ≤ (1314396687259/12500000000000 : ℝ)^4175 := by
    have hnat : (1638628143 : ℕ)^5199*12500000000000^4175 ≤ 1314396687259^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638628143 10000000000 1314396687259 12500000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135772733/10000000000 : ℝ)^5199 ≤ (681469248651/1562500000000 : ℝ)^4175 := by
    have hnat : (5135772733 : ℕ)^5199*1562500000000^4175 ≤ 681469248651^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135772733 10000000000 681469248651 1562500000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534811089/1000000000 : ℝ), (-1638628143/10000000000 : ℝ), (5135772733/10000000000 : ℝ)] ![(22935397283553/50000000000000 : ℝ), (1314396687259/12500000000000 : ℝ), (681469248651/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534811089/1000000000 : ℝ)|^5199 ≤ (22935397283553/50000000000000 : ℝ)^4175
        have hw : |(534811089/1000000000 : ℝ)|=(534811089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1638628143/10000000000 : ℝ)|^5199 ≤ (1314396687259/12500000000000 : ℝ)^4175
        have hw : |(-1638628143/10000000000 : ℝ)|=(1638628143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135772733/10000000000 : ℝ)|^5199 ≤ (681469248651/1562500000000 : ℝ)^4175
        have hw : |(5135772733/10000000000 : ℝ)|=(5135772733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s2_2 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334256951/625000000 : ℝ)*x 0 + (2567886409/5000000000 : ℝ)*x 1 + (-327725519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334256951/625000000 : ℝ)^5199 ≤ (4587079804901/10000000000000 : ℝ)^4175 := by
    have hnat : (334256951 : ℕ)^5199*10000000000000^4175 ≤ 4587079804901^4175*625000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334256951 625000000 4587079804901 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567886409/5000000000 : ℝ)^5199 ≤ (21807016406273/50000000000000 : ℝ)^4175 := by
    have hnat : (2567886409 : ℕ)^5199*50000000000000^4175 ≤ 21807016406273^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567886409 5000000000 21807016406273 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327725519/2000000000 : ℝ)^5199 ≤ (5257584559511/50000000000000 : ℝ)^4175 := by
    have hnat : (327725519 : ℕ)^5199*50000000000000^4175 ≤ 5257584559511^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327725519 2000000000 5257584559511 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334256951/625000000 : ℝ), (2567886409/5000000000 : ℝ), (-327725519/2000000000 : ℝ)] ![(4587079804901/10000000000000 : ℝ), (21807016406273/50000000000000 : ℝ), (5257584559511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334256951/625000000 : ℝ)|^5199 ≤ (4587079804901/10000000000000 : ℝ)^4175
        have hw : |(334256951/625000000 : ℝ)|=(334256951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567886409/5000000000 : ℝ)|^5199 ≤ (21807016406273/50000000000000 : ℝ)^4175
        have hw : |(2567886409/5000000000 : ℝ)|=(2567886409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-327725519/2000000000 : ℝ)|^5199 ≤ (5257584559511/50000000000000 : ℝ)^4175
        have hw : |(-327725519/2000000000 : ℝ)|=(327725519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s2_3 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (128800099/312500000 : ℝ)*x 0 + (731370897/2000000000 : ℝ)*x 1 + (4623460799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128800099/312500000 : ℝ)^5199 ≤ (6632597746909/20000000000000 : ℝ)^4175 := by
    have hnat : (128800099 : ℕ)^5199*20000000000000^4175 ≤ 6632597746909^4175*312500000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128800099 312500000 6632597746909 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (731370897/2000000000 : ℝ)^5199 ≤ (28572703528699/100000000000000 : ℝ)^4175 := by
    have hnat : (731370897 : ℕ)^5199*100000000000000^4175 ≤ 28572703528699^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731370897 2000000000 28572703528699 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4623460799/10000000000 : ℝ)^5199 ≤ (19132153859667/50000000000000 : ℝ)^4175 := by
    have hnat : (4623460799 : ℕ)^5199*50000000000000^4175 ≤ 19132153859667^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4623460799 10000000000 19132153859667 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128800099/312500000 : ℝ), (731370897/2000000000 : ℝ), (4623460799/10000000000 : ℝ)] ![(6632597746909/20000000000000 : ℝ), (28572703528699/100000000000000 : ℝ), (19132153859667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128800099/312500000 : ℝ)|^5199 ≤ (6632597746909/20000000000000 : ℝ)^4175
        have hw : |(128800099/312500000 : ℝ)|=(128800099/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(731370897/2000000000 : ℝ)|^5199 ≤ (28572703528699/100000000000000 : ℝ)^4175
        have hw : |(731370897/2000000000 : ℝ)|=(731370897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4623460799/10000000000 : ℝ)|^5199 ≤ (19132153859667/50000000000000 : ℝ)^4175
        have hw : |(4623460799/10000000000 : ℝ)|=(4623460799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s2_4 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45637713/312500000 : ℝ)*x 0 + (1284887913/2500000000 : ℝ)*x 1 + (5475509221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45637713/312500000 : ℝ)^5199 ≤ (1822110868709/20000000000000 : ℝ)^4175 := by
    have hnat : (45637713 : ℕ)^5199*20000000000000^4175 ≤ 1822110868709^4175*312500000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45637713 312500000 1822110868709 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284887913/2500000000 : ℝ)^5199 ≤ (21826998950207/50000000000000 : ℝ)^4175 := by
    have hnat : (1284887913 : ℕ)^5199*50000000000000^4175 ≤ 21826998950207^4175*2500000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284887913 2500000000 21826998950207 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475509221/10000000000 : ℝ)^5199 ≤ (23617723870349/50000000000000 : ℝ)^4175 := by
    have hnat : (5475509221 : ℕ)^5199*50000000000000^4175 ≤ 23617723870349^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475509221 10000000000 23617723870349 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45637713/312500000 : ℝ), (1284887913/2500000000 : ℝ), (5475509221/10000000000 : ℝ)] ![(1822110868709/20000000000000 : ℝ), (21826998950207/50000000000000 : ℝ), (23617723870349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45637713/312500000 : ℝ)|^5199 ≤ (1822110868709/20000000000000 : ℝ)^4175
        have hw : |(-45637713/312500000 : ℝ)|=(45637713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284887913/2500000000 : ℝ)|^5199 ≤ (21826998950207/50000000000000 : ℝ)^4175
        have hw : |(1284887913/2500000000 : ℝ)|=(1284887913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475509221/10000000000 : ℝ)|^5199 ≤ (23617723870349/50000000000000 : ℝ)^4175
        have hw : |(5475509221/10000000000 : ℝ)|=(5475509221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s2_5 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256200449/10000000000 : ℝ)*x 0 + (-649445739/5000000000 : ℝ)*x 1 + (2737754609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256200449/10000000000 : ℝ)^5199 ≤ (44891205819409/100000000000000 : ℝ)^4175 := by
    have hnat : (5256200449 : ℕ)^5199*100000000000000^4175 ≤ 44891205819409^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256200449 10000000000 44891205819409 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649445739/5000000000 : ℝ)^5199 ≤ (1574669290883/20000000000000 : ℝ)^4175 := by
    have hnat : (649445739 : ℕ)^5199*20000000000000^4175 ≤ 1574669290883^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649445739 5000000000 1574669290883 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737754609/5000000000 : ℝ)^5199 ≤ (4723544770847/10000000000000 : ℝ)^4175 := by
    have hnat : (2737754609 : ℕ)^5199*10000000000000^4175 ≤ 4723544770847^4175*5000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737754609 5000000000 4723544770847 10000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256200449/10000000000 : ℝ), (-649445739/5000000000 : ℝ), (2737754609/5000000000 : ℝ)] ![(44891205819409/100000000000000 : ℝ), (1574669290883/20000000000000 : ℝ), (4723544770847/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256200449/10000000000 : ℝ)|^5199 ≤ (44891205819409/100000000000000 : ℝ)^4175
        have hw : |(5256200449/10000000000 : ℝ)|=(5256200449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649445739/5000000000 : ℝ)|^5199 ≤ (1574669290883/20000000000000 : ℝ)^4175
        have hw : |(-649445739/5000000000 : ℝ)|=(649445739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737754609/5000000000 : ℝ)|^5199 ≤ (4723544770847/10000000000000 : ℝ)^4175
        have hw : |(2737754609/5000000000 : ℝ)|=(2737754609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s2_6 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105124009/200000000 : ℝ)*x 0 + (1095101843/2000000000 : ℝ)*x 1 + (-1298891481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105124009/200000000 : ℝ)^5199 ≤ (8978241166009/20000000000000 : ℝ)^4175 := by
    have hnat : (105124009 : ℕ)^5199*20000000000000^4175 ≤ 8978241166009^4175*200000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105124009 200000000 8978241166009 20000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095101843/2000000000 : ℝ)^5199 ≤ (47235447676243/100000000000000 : ℝ)^4175 := by
    have hnat : (1095101843 : ℕ)^5199*100000000000000^4175 ≤ 47235447676243^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095101843 2000000000 47235447676243 100000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298891481/10000000000 : ℝ)^5199 ≤ (393667323853/5000000000000 : ℝ)^4175 := by
    have hnat : (1298891481 : ℕ)^5199*5000000000000^4175 ≤ 393667323853^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298891481 10000000000 393667323853 5000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105124009/200000000 : ℝ), (1095101843/2000000000 : ℝ), (-1298891481/10000000000 : ℝ)] ![(8978241166009/20000000000000 : ℝ), (47235447676243/100000000000000 : ℝ), (393667323853/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105124009/200000000 : ℝ)|^5199 ≤ (8978241166009/20000000000000 : ℝ)^4175
        have hw : |(105124009/200000000 : ℝ)|=(105124009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095101843/2000000000 : ℝ)|^5199 ≤ (47235447676243/100000000000000 : ℝ)^4175
        have hw : |(1095101843/2000000000 : ℝ)|=(1095101843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1298891481/10000000000 : ℝ)|^5199 ≤ (393667323853/5000000000000 : ℝ)^4175
        have hw : |(-1298891481/10000000000 : ℝ)|=(1298891481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1697_s2_7 (p : ℝ) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (824410587/2000000000 : ℝ)*x 0 + (4612829847/10000000000 : ℝ)*x 1 + (146705787/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824410587/2000000000 : ℝ)^5199 ≤ (8291873821217/25000000000000 : ℝ)^4175 := by
    have hnat : (824410587 : ℕ)^5199*25000000000000^4175 ≤ 8291873821217^4175*2000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824410587 2000000000 8291873821217 25000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4612829847/10000000000 : ℝ)^5199 ≤ (596168376103/1562500000000 : ℝ)^4175 := by
    have hnat : (4612829847 : ℕ)^5199*1562500000000^4175 ≤ 596168376103^4175*10000000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612829847 10000000000 596168376103 1562500000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146705787/400000000 : ℝ)^5199 ≤ (14338864312983/50000000000000 : ℝ)^4175 := by
    have hnat : (146705787 : ℕ)^5199*50000000000000^4175 ≤ 14338864312983^4175*400000000^5199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146705787 400000000 14338864312983 50000000000000 5199 4175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5199/1024 : ℝ)) 5199 4175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(824410587/2000000000 : ℝ), (4612829847/10000000000 : ℝ), (146705787/400000000 : ℝ)] ![(8291873821217/25000000000000 : ℝ), (596168376103/1562500000000 : ℝ), (14338864312983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(824410587/2000000000 : ℝ)|^5199 ≤ (8291873821217/25000000000000 : ℝ)^4175
        have hw : |(824410587/2000000000 : ℝ)|=(824410587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4612829847/10000000000 : ℝ)|^5199 ≤ (596168376103/1562500000000 : ℝ)^4175
        have hw : |(4612829847/10000000000 : ℝ)|=(4612829847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146705787/400000000 : ℝ)|^5199 ≤ (14338864312983/50000000000000 : ℝ)^4175
        have hw : |(146705787/400000000 : ℝ)|=(146705787/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1697_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1909/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9883/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17203/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1909/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1909/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1909/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1909/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1909/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1909/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1909/20000 : ℝ) ^ (5191/1024 : ℝ) ≤ (336597957113837/50000000000000000000 : ℝ) := by
    have hpowers : (1909/20000 : ℝ)^5191 ≤ (336597957113837/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1909 : ℕ)^5191*50000000000000000000^1024 ≤ 336597957113837^1024*20000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1909 20000 336597957113837 50000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1909/20000 : ℝ)) (X := (336597957113837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17593/100000 : ℝ) ^ (5191/1024 : ℝ) ≤ (747041024997069/5000000000000000000 : ℝ) := by
    have hpowers : (17593/100000 : ℝ)^5191 ≤ (747041024997069/5000000000000000000 : ℝ)^1024 := by
      have hnat : (17593 : ℕ)^5191*5000000000000000000^1024 ≤ 747041024997069^1024*100000^5191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17593 100000 747041024997069 5000000000000000000 5191 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17593/100000 : ℝ)) (X := (747041024997069/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000336597957113837/25000000000000000000 : ℝ) ≤ (10000026559387053/10000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (25000336597957113837/25000000000000000000 : ℝ)^1024 ≤ (10000026559387053/10000000000000000 : ℝ)^5191 := by
      have hnat : (25000336597957113837 : ℕ)^1024*10000000000000000^5191 ≤ 10000026559387053^5191*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000336597957113837 25000000000000000000 10000026559387053 10000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000026559387053/10000000000000000 : ℝ)) (X := (25000336597957113837/25000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007807008207084527/50000000000000000000 : ℝ) ≤ (10000307989807223/10000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (50007807008207084527/50000000000000000000 : ℝ)^1024 ≤ (10000307989807223/10000000000000000 : ℝ)^5191 := by
      have hnat : (50007807008207084527 : ℕ)^1024*10000000000000000^5191 ≤ 10000307989807223^5191*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007807008207084527 50000000000000000000 10000307989807223 10000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000307989807223/10000000000000000 : ℝ)) (X := (50007807008207084527/50000000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2500747041024997069/2500000000000000000 : ℝ) ≤ (10000589420227393/10000000000000000 : ℝ) ^ (5191/1024 : ℝ) := by
    have hpowers : (2500747041024997069/2500000000000000000 : ℝ)^1024 ≤ (10000589420227393/10000000000000000 : ℝ)^5191 := by
      have hnat : (2500747041024997069 : ℕ)^1024*10000000000000000^5191 ≤ 10000589420227393^5191*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500747041024997069 2500000000000000000 10000589420227393 10000000000000000 1024 5191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000589420227393/10000000000000000 : ℝ)) (X := (2500747041024997069/2500000000000000000 : ℝ)) (by norm_num) 5191 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(336597957113837/50000000000000000000 : ℝ) ≤ ((20118710310806489311/20120000000000000000 : ℝ)+2*(28143042017/80480000000000 : ℝ)*(1909/20000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (20118710310806489311/20120000000000000000 : ℝ)+2*(28143042017/80480000000000 : ℝ)*(1909/20000 : ℝ)=(10000026559387053/10000000000000000 : ℝ) by norm_num, show 1+2*(336597957113837/50000000000000000000 : ℝ)=(25000336597957113837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(747041024997069/5000000000000000000 : ℝ)+(336597957113837/50000000000000000000 : ℝ) ≤ ((20118710310806489311/20120000000000000000 : ℝ)+(28143042017/80480000000000 : ℝ)*((17593/100000 : ℝ)+(1909/20000 : ℝ)))^(5191/1024 : ℝ) := by
    rw [show (20118710310806489311/20120000000000000000 : ℝ)+(28143042017/80480000000000 : ℝ)*((17593/100000 : ℝ)+(1909/20000 : ℝ))=(10000307989807223/10000000000000000 : ℝ) by norm_num, show 1+(747041024997069/5000000000000000000 : ℝ)+(336597957113837/50000000000000000000 : ℝ)=(50007807008207084527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(747041024997069/5000000000000000000 : ℝ) ≤ ((20118710310806489311/20120000000000000000 : ℝ)+2*(28143042017/80480000000000 : ℝ)*(17593/100000 : ℝ))^(5191/1024 : ℝ) := by
    rw [show (20118710310806489311/20120000000000000000 : ℝ)+2*(28143042017/80480000000000 : ℝ)*(17593/100000 : ℝ)=(10000589420227393/10000000000000000 : ℝ) by norm_num, show 1+2*(747041024997069/5000000000000000000 : ℝ)=(2500747041024997069/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20118710310806489311/20120000000000000000 : ℝ)*(X 1 0+X 2 0)+(28143042017/80480000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (1909/20000 : ℝ)) (hi := (17593/100000 : ℝ)) (c := (20118710310806489311/20120000000000000000 : ℝ)) (alpha := (28143042017/80480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20118710310806489311/20120000000000000000 : ℝ)*(X 0 1+X 2 1)+(28143042017/80480000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (1909/20000 : ℝ)) (hi := (17593/100000 : ℝ)) (c := (20118710310806489311/20120000000000000000 : ℝ)) (alpha := (28143042017/80480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20118710310806489311/20120000000000000000 : ℝ)*(X 0 2+X 1 2)+(28143042017/80480000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5191/1024 : ℝ)) (lo := (1909/20000 : ℝ)) (hi := (17593/100000 : ℝ)) (c := (20118710310806489311/20120000000000000000 : ℝ)) (alpha := (28143042017/80480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1460246793/10000000000 : ℝ)*X 0 0+(5479344843/10000000000 : ℝ)*X 0 1+(5135772851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534811089/1000000000 : ℝ)*X 1 0+(-1638628143/10000000000 : ℝ)*X 1 1+(5135772733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334256951/625000000 : ℝ)*X 2 0+(2567886409/5000000000 : ℝ)*X 2 1+(-327725519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((128800099/312500000 : ℝ)*X 0 0+(731370897/2000000000 : ℝ)*X 0 1+(4623460799/10000000000 : ℝ)*X 0 2+(128800099/312500000 : ℝ)*X 1 0+(731370897/2000000000 : ℝ)*X 1 1+(4623460799/10000000000 : ℝ)*X 1 2+(128800099/312500000 : ℝ)*X 2 0+(731370897/2000000000 : ℝ)*X 2 1+(4623460799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-45637713/312500000 : ℝ)*X 0 0+(1284887913/2500000000 : ℝ)*X 0 1+(5475509221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256200449/10000000000 : ℝ)*X 1 0+(-649445739/5000000000 : ℝ)*X 1 1+(2737754609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105124009/200000000 : ℝ)*X 2 0+(1095101843/2000000000 : ℝ)*X 2 1+(-1298891481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((824410587/2000000000 : ℝ)*X 0 0+(4612829847/10000000000 : ℝ)*X 0 1+(146705787/400000000 : ℝ)*X 0 2+(824410587/2000000000 : ℝ)*X 1 0+(4612829847/10000000000 : ℝ)*X 1 1+(146705787/400000000 : ℝ)*X 1 2+(824410587/2000000000 : ℝ)*X 2 0+(4612829847/10000000000 : ℝ)*X 2 1+(146705787/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1697_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3584398694970243088724875569/503000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91924823/10000000000000 : ℝ)*(base19) + (479280239/50000000000000 : ℝ)*(base23) + (39424647/50000000000000 : ℝ)*(lower2) + (54746131/25000000000000 : ℝ)*(upper5) + (986292697006693/50000000000000 : ℝ)*(major0) + (986292697006693/50000000000000 : ℝ)*(major1) + (986292697006693/50000000000000 : ℝ)*(major2) + (145530245782543/5000000000000 : ℝ)*(sp0) + (1455308073470049/50000000000000 : ℝ)*(sp1) + (1455308325155099/50000000000000 : ℝ)*(sp2) + (517275244013659/50000000000000 : ℝ)*(sp3) + (1586652477/12500000000000 : ℝ)*(sp4) + (135670587/25000000000000 : ℝ)*(sp5) + (2453594071/100000000000000 : ℝ)*(sp7) + (1034552941621389/100000000000000 : ℝ)*(f.failure) + (727654402217669/25000000000000 : ℝ)*(f.sum) + (1724627266779/402400000000000000000000000 : ℝ)*base66 + (1751438159271208523/1006000000000000000000000000000000 : ℝ)*base67 + (1256546933672791477/1006000000000000000000000000000000 : ℝ)*base70 + (4265069486140791477/1006000000000000000000000000000000 : ℝ)*base72 + (4942741401673/2012000000000000000000000000 : ℝ)*base73 + (1618695125315208523/1006000000000000000000000000000000 : ℝ)*base75 + (4556346017916791477/1006000000000000000000000000000000 : ℝ)*base78 + (165139674440791477/1006000000000000000000000000000000 : ℝ)*base80 + (495285443417/2012000000000000000000000000 : ℝ)*base81 + (17853091/10000000000000000000000 : ℝ)*base89 + (17853091/10000000000000000000000 : ℝ)*base91 + (17853091/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (469028641353982688400252969/100600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33331479/5000000000000 : ℝ)*(base19) + (178541749/25000000000000 : ℝ)*(base23) + (6284071/6250000000000 : ℝ)*(upper3) + (1055733/5000000000000 : ℝ)*(lower4) + (97462173/100000000000000 : ℝ)*(upper5) + (201727995114493/10000000000000 : ℝ)*(major0) + (201727995114493/10000000000000 : ℝ)*(major1) + (201727995114493/10000000000000 : ℝ)*(major2) + (1473037501/25000000000000 : ℝ)*(sp1) + (3140508727/50000000000000 : ℝ)*(sp2) + (372070756623353/12500000000000 : ℝ)*(sp4) + (74413987355181/2500000000000 : ℝ)*(sp5) + (23812472462419/800000000000 : ℝ)*(sp6) + (528996846946307/50000000000000 : ℝ)*(sp7) + (528996846946307/50000000000000 : ℝ)*(f.failure) + (372070756623353/12500000000000 : ℝ)*(f.sum) + (4170435093433/2012000000000000000000000000 : ℝ)*base65 + (23455189246265677/201200000000000000000000000000000 : ℝ)*base68 + (555196860343865677/201200000000000000000000000000000 : ℝ)*base70 + (725847190228934323/201200000000000000000000000000000 : ℝ)*base71 + (1046891488713/2012000000000000000000000000 : ℝ)*base73 + (576901340121465677/201200000000000000000000000000000 : ℝ)*base76 + (37292805236134323/201200000000000000000000000000000 : ℝ)*base77 + (2191328400345065677/201200000000000000000000000000000 : ℝ)*base80 + (495076493487/402400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (31561933/5000000000000000000000 : ℝ)*base89 + (31561933/5000000000000000000000 : ℝ)*base91 + (31561933/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1697_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1909/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1697_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1697_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1697_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1697_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1697_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5191/1024 : ℝ) ≤ p) (hpb : p ≤ (5199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190670319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9883/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17203/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1697_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
