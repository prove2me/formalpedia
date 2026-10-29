-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1696_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:43:36.922415+00:00
-- url     : https://prove2.me/submissions/5776fdc6-427e-4ef2-ac96-64b8c3985aa3

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
theorem support_rectangle_w1696_s0_0 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-689422917/5000000000 : ℝ)*x 0 + (572675533/1000000000 : ℝ)*x 1 + (15452559/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689422917/5000000000 : ℝ)^5191 ≤ (8473444884899/100000000000000 : ℝ)^4167 := by
    have hnat : (689422917 : ℕ)^5191*100000000000000^4167 ≤ 8473444884899^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689422917 5000000000 8473444884899 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572675533/1000000000 : ℝ)^5191 ≤ (12484093748037/25000000000000 : ℝ)^4167 := by
    have hnat : (572675533 : ℕ)^5191*25000000000000^4167 ≤ 12484093748037^4167*1000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572675533 1000000000 12484093748037 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15452559/31250000 : ℝ)^5191 ≤ (41590180107829/100000000000000 : ℝ)^4167 := by
    have hnat : (15452559 : ℕ)^5191*100000000000000^4167 ≤ 41590180107829^4167*31250000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15452559 31250000 41590180107829 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-689422917/5000000000 : ℝ), (572675533/1000000000 : ℝ), (15452559/31250000 : ℝ)] ![(8473444884899/100000000000000 : ℝ), (12484093748037/25000000000000 : ℝ), (41590180107829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-689422917/5000000000 : ℝ)|^5191 ≤ (8473444884899/100000000000000 : ℝ)^4167
        have hw : |(-689422917/5000000000 : ℝ)|=(689422917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572675533/1000000000 : ℝ)|^5191 ≤ (12484093748037/25000000000000 : ℝ)^4167
        have hw : |(572675533/1000000000 : ℝ)|=(572675533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15452559/31250000 : ℝ)|^5191 ≤ (41590180107829/100000000000000 : ℝ)^4167
        have hw : |(15452559/31250000 : ℝ)|=(15452559/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s0_1 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707114193/5000000000 : ℝ)*x 0 + (-72170589/400000000 : ℝ)*x 1 + (4944819827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707114193/5000000000 : ℝ)^5191 ≤ (4656458725379/10000000000000 : ℝ)^4167 := by
    have hnat : (2707114193 : ℕ)^5191*10000000000000^4167 ≤ 4656458725379^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707114193 5000000000 4656458725379 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72170589/400000000 : ℝ)^5191 ≤ (5922611352471/50000000000000 : ℝ)^4167 := by
    have hnat : (72170589 : ℕ)^5191*50000000000000^4167 ≤ 5922611352471^4167*400000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72170589 400000000 5922611352471 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4944819827/10000000000 : ℝ)^5191 ≤ (2599386876891/6250000000000 : ℝ)^4167 := by
    have hnat : (4944819827 : ℕ)^5191*6250000000000^4167 ≤ 2599386876891^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4944819827 10000000000 2599386876891 6250000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707114193/5000000000 : ℝ), (-72170589/400000000 : ℝ), (4944819827/10000000000 : ℝ)] ![(4656458725379/10000000000000 : ℝ), (5922611352471/50000000000000 : ℝ), (2599386876891/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707114193/5000000000 : ℝ)|^5191 ≤ (4656458725379/10000000000000 : ℝ)^4167
        have hw : |(2707114193/5000000000 : ℝ)|=(2707114193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72170589/400000000 : ℝ)|^5191 ≤ (5922611352471/50000000000000 : ℝ)^4167
        have hw : |(-72170589/400000000 : ℝ)|=(72170589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4944819827/10000000000 : ℝ)|^5191 ≤ (2599386876891/6250000000000 : ℝ)^4167
        have hw : |(4944819827/10000000000 : ℝ)|=(4944819827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s0_2 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5414230983/10000000000 : ℝ)*x 0 + (4944819047/10000000000 : ℝ)*x 1 + (-1804262321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414230983/10000000000 : ℝ)^5191 ≤ (23282307538867/50000000000000 : ℝ)^4167 := by
    have hnat : (5414230983 : ℕ)^5191*50000000000000^4167 ≤ 23282307538867^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414230983 10000000000 23282307538867 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4944819047/10000000000 : ℝ)^5191 ≤ (10397545464403/25000000000000 : ℝ)^4167 := by
    have hnat : (4944819047 : ℕ)^5191*25000000000000^4167 ≤ 10397545464403^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4944819047 10000000000 10397545464403 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1804262321/10000000000 : ℝ)^5191 ≤ (5922601521987/50000000000000 : ℝ)^4167 := by
    have hnat : (1804262321 : ℕ)^5191*50000000000000^4167 ≤ 5922601521987^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804262321 10000000000 5922601521987 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414230983/10000000000 : ℝ), (4944819047/10000000000 : ℝ), (-1804262321/10000000000 : ℝ)] ![(23282307538867/50000000000000 : ℝ), (10397545464403/25000000000000 : ℝ), (5922601521987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414230983/10000000000 : ℝ)|^5191 ≤ (23282307538867/50000000000000 : ℝ)^4167
        have hw : |(5414230983/10000000000 : ℝ)|=(5414230983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4944819047/10000000000 : ℝ)|^5191 ≤ (10397545464403/25000000000000 : ℝ)^4167
        have hw : |(4944819047/10000000000 : ℝ)|=(4944819047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1804262321/10000000000 : ℝ)|^5191 ≤ (5922601521987/50000000000000 : ℝ)^4167
        have hw : |(-1804262321/10000000000 : ℝ)|=(1804262321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s0_3 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (506431379/1250000000 : ℝ)*x 0 + (3050772417/10000000000 : ℝ)*x 1 + (1311381899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506431379/1250000000 : ℝ)^5191 ≤ (32447757518391/100000000000000 : ℝ)^4167 := by
    have hnat : (506431379 : ℕ)^5191*100000000000000^4167 ≤ 32447757518391^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506431379 1250000000 32447757518391 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3050772417/10000000000 : ℝ)^5191 ≤ (22788120246001/100000000000000 : ℝ)^4167 := by
    have hnat : (3050772417 : ℕ)^5191*100000000000000^4167 ≤ 22788120246001^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3050772417 10000000000 22788120246001 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311381899/2500000000 : ℝ)^5191 ≤ (1398878819249/3125000000000 : ℝ)^4167 := by
    have hnat : (1311381899 : ℕ)^5191*3125000000000^4167 ≤ 1398878819249^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311381899 2500000000 1398878819249 3125000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(506431379/1250000000 : ℝ), (3050772417/10000000000 : ℝ), (1311381899/2500000000 : ℝ)] ![(32447757518391/100000000000000 : ℝ), (22788120246001/100000000000000 : ℝ), (1398878819249/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(506431379/1250000000 : ℝ)|^5191 ≤ (32447757518391/100000000000000 : ℝ)^4167
        have hw : |(506431379/1250000000 : ℝ)|=(506431379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3050772417/10000000000 : ℝ)|^5191 ≤ (22788120246001/100000000000000 : ℝ)^4167
        have hw : |(3050772417/10000000000 : ℝ)|=(3050772417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311381899/2500000000 : ℝ)|^5191 ≤ (1398878819249/3125000000000 : ℝ)^4167
        have hw : |(1311381899/2500000000 : ℝ)|=(1311381899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s0_4 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1380747341/10000000000 : ℝ)*x 0 + (2482162361/5000000000 : ℝ)*x 1 + (5706582489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380747341/10000000000 : ℝ)^5191 ≤ (1697600855867/20000000000000 : ℝ)^4167 := by
    have hnat : (1380747341 : ℕ)^5191*20000000000000^4167 ≤ 1697600855867^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380747341 10000000000 1697600855867 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482162361/5000000000 : ℝ)^5191 ≤ (41794656361733/100000000000000 : ℝ)^4167 := by
    have hnat : (2482162361 : ℕ)^5191*100000000000000^4167 ≤ 41794656361733^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482162361 5000000000 41794656361733 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5706582489/10000000000 : ℝ)^5191 ≤ (6214667418137/12500000000000 : ℝ)^4167 := by
    have hnat : (5706582489 : ℕ)^5191*12500000000000^4167 ≤ 6214667418137^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706582489 10000000000 6214667418137 12500000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1380747341/10000000000 : ℝ), (2482162361/5000000000 : ℝ), (5706582489/10000000000 : ℝ)] ![(1697600855867/20000000000000 : ℝ), (41794656361733/100000000000000 : ℝ), (6214667418137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1380747341/10000000000 : ℝ)|^5191 ≤ (1697600855867/20000000000000 : ℝ)^4167
        have hw : |(-1380747341/10000000000 : ℝ)|=(1380747341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2482162361/5000000000 : ℝ)|^5191 ≤ (41794656361733/100000000000000 : ℝ)^4167
        have hw : |(2482162361/5000000000 : ℝ)|=(2482162361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5706582489/10000000000 : ℝ)|^5191 ≤ (6214667418137/12500000000000 : ℝ)^4167
        have hw : |(5706582489/10000000000 : ℝ)|=(5706582489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s0_5 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1300493883/2500000000 : ℝ)*x 0 + (-104250081/1000000000 : ℝ)*x 1 + (5706582581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300493883/2500000000 : ℝ)^5191 ≤ (4430159960997/10000000000000 : ℝ)^4167 := by
    have hnat : (1300493883 : ℕ)^5191*10000000000000^4167 ≤ 4430159960997^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300493883 2500000000 4430159960997 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104250081/1000000000 : ℝ)^5191 ≤ (5981060029487/100000000000000 : ℝ)^4167 := by
    have hnat : (104250081 : ℕ)^5191*100000000000000^4167 ≤ 5981060029487^4167*1000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104250081 1000000000 5981060029487 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5706582581/10000000000 : ℝ)^5191 ≤ (24858670171797/50000000000000 : ℝ)^4167 := by
    have hnat : (5706582581 : ℕ)^5191*50000000000000^4167 ≤ 24858670171797^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706582581 10000000000 24858670171797 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300493883/2500000000 : ℝ), (-104250081/1000000000 : ℝ), (5706582581/10000000000 : ℝ)] ![(4430159960997/10000000000000 : ℝ), (5981060029487/100000000000000 : ℝ), (24858670171797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300493883/2500000000 : ℝ)|^5191 ≤ (4430159960997/10000000000000 : ℝ)^4167
        have hw : |(1300493883/2500000000 : ℝ)|=(1300493883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104250081/1000000000 : ℝ)|^5191 ≤ (5981060029487/100000000000000 : ℝ)^4167
        have hw : |(-104250081/1000000000 : ℝ)|=(104250081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5706582581/10000000000 : ℝ)|^5191 ≤ (24858670171797/50000000000000 : ℝ)^4167
        have hw : |(5706582581/10000000000 : ℝ)|=(5706582581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s0_6 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260098767/500000000 : ℝ)*x 0 + (1426645773/2500000000 : ℝ)*x 1 + (-1042500319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260098767/500000000 : ℝ)^5191 ≤ (22150798786511/50000000000000 : ℝ)^4167 := by
    have hnat : (260098767 : ℕ)^5191*50000000000000^4167 ≤ 22150798786511^4167*500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260098767 500000000 22150798786511 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426645773/2500000000 : ℝ)^5191 ≤ (49717345889599/100000000000000 : ℝ)^4167 := by
    have hnat : (1426645773 : ℕ)^5191*100000000000000^4167 ≤ 49717345889599^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426645773 2500000000 49717345889599 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042500319/10000000000 : ℝ)^5191 ≤ (2990528260133/50000000000000 : ℝ)^4167 := by
    have hnat : (1042500319 : ℕ)^5191*50000000000000^4167 ≤ 2990528260133^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042500319 10000000000 2990528260133 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260098767/500000000 : ℝ), (1426645773/2500000000 : ℝ), (-1042500319/10000000000 : ℝ)] ![(22150798786511/50000000000000 : ℝ), (49717345889599/100000000000000 : ℝ), (2990528260133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260098767/500000000 : ℝ)|^5191 ≤ (22150798786511/50000000000000 : ℝ)^4167
        have hw : |(260098767/500000000 : ℝ)|=(260098767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426645773/2500000000 : ℝ)|^5191 ≤ (49717345889599/100000000000000 : ℝ)^4167
        have hw : |(1426645773/2500000000 : ℝ)|=(1426645773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1042500319/10000000000 : ℝ)|^5191 ≤ (2990528260133/50000000000000 : ℝ)^4167
        have hw : |(-1042500319/10000000000 : ℝ)|=(1042500319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s0_7 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4056788023/10000000000 : ℝ)*x 0 + (5190775383/10000000000 : ℝ)*x 1 + (97106019/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4056788023/10000000000 : ℝ)^5191 ≤ (8125253373877/25000000000000 : ℝ)^4167 := by
    have hnat : (4056788023 : ℕ)^5191*25000000000000^4167 ≤ 8125253373877^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4056788023 10000000000 8125253373877 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190775383/10000000000 : ℝ)^5191 ≤ (44182807536521/100000000000000 : ℝ)^4167 := by
    have hnat : (5190775383 : ℕ)^5191*100000000000000^4167 ≤ 44182807536521^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190775383 10000000000 44182807536521 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97106019/312500000 : ℝ)^5191 ≤ (5829044737931/25000000000000 : ℝ)^4167 := by
    have hnat : (97106019 : ℕ)^5191*25000000000000^4167 ≤ 5829044737931^4167*312500000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97106019 312500000 5829044737931 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4056788023/10000000000 : ℝ), (5190775383/10000000000 : ℝ), (97106019/312500000 : ℝ)] ![(8125253373877/25000000000000 : ℝ), (44182807536521/100000000000000 : ℝ), (5829044737931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4056788023/10000000000 : ℝ)|^5191 ≤ (8125253373877/25000000000000 : ℝ)^4167
        have hw : |(4056788023/10000000000 : ℝ)|=(4056788023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190775383/10000000000 : ℝ)|^5191 ≤ (44182807536521/100000000000000 : ℝ)^4167
        have hw : |(5190775383/10000000000 : ℝ)|=(5190775383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(97106019/312500000 : ℝ)|^5191 ≤ (5829044737931/25000000000000 : ℝ)^4167
        have hw : |(97106019/312500000 : ℝ)|=(97106019/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1696_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (9/160 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11207/50000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5183/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5183 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5183*1^1024 ≤ 0^1024*1^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5183/1024 : ℝ) ≤ (193574129556792453/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5183 ≤ (193574129556792453/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5183*20000000000000000000^1024 ≤ 193574129556792453^1024*5^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 193574129556792453 20000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (193574129556792453/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5183 := by
      have hnat : (1 : ℕ)^1024*1^5183 ≤ 1^5183*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20193574129556792453/20000000000000000000 : ℝ) ≤ (400761931768113/400000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (20193574129556792453/20000000000000000000 : ℝ)^1024 ≤ (400761931768113/400000000000000 : ℝ)^5183 := by
      have hnat : (20193574129556792453 : ℕ)^1024*400000000000000^5183 ≤ 400761931768113^5183*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20193574129556792453 20000000000000000000 400761931768113 400000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400761931768113/400000000000000 : ℝ)) (X := (20193574129556792453/20000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10193574129556792453/10000000000000000000 : ℝ) ≤ (200761931768113/200000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (10193574129556792453/10000000000000000000 : ℝ)^1024 ≤ (200761931768113/200000000000000 : ℝ)^5183 := by
      have hnat : (10193574129556792453 : ℕ)^1024*200000000000000^5183 ≤ 200761931768113^5183*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10193574129556792453 10000000000000000000 200761931768113 200000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200761931768113/200000000000000 : ℝ)) (X := (10193574129556792453/10000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(761931768113/160000000000000 : ℝ)*(0 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(761931768113/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(193574129556792453/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(761931768113/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5183/1024 : ℝ) := by
    rw [show (1 : ℝ)+(761931768113/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(400761931768113/400000000000000 : ℝ) by norm_num, show 1+(193574129556792453/20000000000000000000 : ℝ)+(0 : ℝ)=(20193574129556792453/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(193574129556792453/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(761931768113/160000000000000 : ℝ)*(2/5 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(761931768113/160000000000000 : ℝ)*(2/5 : ℝ)=(200761931768113/200000000000000 : ℝ) by norm_num, show 1+2*(193574129556792453/20000000000000000000 : ℝ)=(10193574129556792453/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(761931768113/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (761931768113/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(761931768113/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (761931768113/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(761931768113/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (761931768113/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-689422917/5000000000 : ℝ)*X 0 0+(572675533/1000000000 : ℝ)*X 0 1+(15452559/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2707114193/5000000000 : ℝ)*X 1 0+(-72170589/400000000 : ℝ)*X 1 1+(4944819827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414230983/10000000000 : ℝ)*X 2 0+(4944819047/10000000000 : ℝ)*X 2 1+(-1804262321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((506431379/1250000000 : ℝ)*X 0 0+(3050772417/10000000000 : ℝ)*X 0 1+(1311381899/2500000000 : ℝ)*X 0 2+(506431379/1250000000 : ℝ)*X 1 0+(3050772417/10000000000 : ℝ)*X 1 1+(1311381899/2500000000 : ℝ)*X 1 2+(506431379/1250000000 : ℝ)*X 2 0+(3050772417/10000000000 : ℝ)*X 2 1+(1311381899/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1380747341/10000000000 : ℝ)*X 0 0+(2482162361/5000000000 : ℝ)*X 0 1+(5706582489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1300493883/2500000000 : ℝ)*X 1 0+(-104250081/1000000000 : ℝ)*X 1 1+(5706582581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((260098767/500000000 : ℝ)*X 2 0+(1426645773/2500000000 : ℝ)*X 2 1+(-1042500319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4056788023/10000000000 : ℝ)*X 0 0+(5190775383/10000000000 : ℝ)*X 0 1+(97106019/312500000 : ℝ)*X 0 2+(4056788023/10000000000 : ℝ)*X 1 0+(5190775383/10000000000 : ℝ)*X 1 1+(97106019/312500000 : ℝ)*X 1 2+(4056788023/10000000000 : ℝ)*X 2 0+(5190775383/10000000000 : ℝ)*X 2 1+(97106019/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37408914740329689916041/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1165287/100000000000000 : ℝ)*(base1) + (1328919291/100000000000000 : ℝ)*(base19) + (173154043/10000000000000 : ℝ)*(base23) + (42162799/20000000000000 : ℝ)*(base24) + (344743721/100000000000000 : ℝ)*(upper5) + (433632601930419/50000000000000 : ℝ)*(major0) + (433632601930419/50000000000000 : ℝ)*(major1) + (433632601930419/50000000000000 : ℝ)*(major2) + (1278881766292047/100000000000000 : ℝ)*(sp0) + (639445418716569/50000000000000 : ℝ)*(sp1) + (639445111999003/50000000000000 : ℝ)*(sp2) + (28477190413817/6250000000000 : ℝ)*(sp3) + (10401225669/100000000000000 : ℝ)*(sp4) + (2881841923/100000000000000 : ℝ)*(sp7) + (227818964814141/50000000000000 : ℝ)*(f.failure) + (127889216635243/10000000000000 : ℝ)*(f.sum) + (862555894653/4000000000000000000000000000 : ℝ)*base66 + (29761547558653/8000000000000000000000000000 : ℝ)*base68 + (19741944153347/8000000000000000000000000000 : ℝ)*base69 + (6368150521347/8000000000000000000000000000 : ℝ)*base71 + (21853913002653/4000000000000000000000000000 : ℝ)*base74 + (50805387153347/8000000000000000000000000000 : ℝ)*base75 + (50261966518653/8000000000000000000000000000 : ℝ)*base78 + (64539713590653/8000000000000000000000000000 : ℝ)*base80 + (18922164249347/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (51056811/5000000000000000000000 : ℝ)*base89 + (51056811/5000000000000000000000 : ℝ)*base91 + (51056811/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15345840572761011052371/1600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2220329497/100000000000000 : ℝ)*(base19) + (2231502227/100000000000000 : ℝ)*(base23) + (9222873/100000000000000 : ℝ)*(upper2) + (90896313/25000000000000 : ℝ)*(upper3) + (80936641/25000000000000 : ℝ)*(upper5) + (182722948329089/20000000000000 : ℝ)*(major0) + (182722948329089/20000000000000 : ℝ)*(major1) + (182722948329089/20000000000000 : ℝ)*(major2) + (3951948891/50000000000000 : ℝ)*(sp1) + (4480884709/50000000000000 : ℝ)*(sp2) + (1347240427143953/100000000000000 : ℝ)*(sp4) + (673615151458337/50000000000000 : ℝ)*(sp5) + (1347229233872309/100000000000000 : ℝ)*(sp6) + (1499964801381/312500000000 : ℝ)*(sp7) + (1499964801381/312500000000 : ℝ)*(f.failure) + (1347240427143953/100000000000000 : ℝ)*(f.sum) + (7341328239857/1600000000000000000000000000 : ℝ)*base65 + (6077683975857/3200000000000000000000000000 : ℝ)*base67 + (25363611867343/3200000000000000000000000000 : ℝ)*base70 + (4625750116943/3200000000000000000000000000 : ℝ)*base72 + (7489705387057/1600000000000000000000000000 : ℝ)*base73 + (12197980798543/3200000000000000000000000000 : ℝ)*base76 + (10496718225743/3200000000000000000000000000 : ℝ)*base78 + (24143749649743/3200000000000000000000000000 : ℝ)*base80 + (3765738038543/1600000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (19649/31250000000000000000 : ℝ)*base90 + (19649/31250000000000000000 : ℝ)*base92 + (19649/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1696_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/160 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11207/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1696_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1696_s1_0 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-729692983/5000000000 : ℝ)*x 0 + (5499009803/10000000000 : ℝ)*x 1 + (8191599/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (729692983/5000000000 : ℝ)^5191 ≤ (9094379171507/100000000000000 : ℝ)^4167 := by
    have hnat : (729692983 : ℕ)^5191*100000000000000^4167 ≤ 9094379171507^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729692983 5000000000 9094379171507 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499009803/10000000000 : ℝ)^5191 ≤ (47474665880147/100000000000000 : ℝ)^4167 := by
    have hnat : (5499009803 : ℕ)^5191*100000000000000^4167 ≤ 47474665880147^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499009803 10000000000 47474665880147 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8191599/16000000 : ℝ)^5191 ≤ (21715477469233/50000000000000 : ℝ)^4167 := by
    have hnat : (8191599 : ℕ)^5191*50000000000000^4167 ≤ 21715477469233^4167*16000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8191599 16000000 21715477469233 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-729692983/5000000000 : ℝ), (5499009803/10000000000 : ℝ), (8191599/16000000 : ℝ)] ![(9094379171507/100000000000000 : ℝ), (47474665880147/100000000000000 : ℝ), (21715477469233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-729692983/5000000000 : ℝ)|^5191 ≤ (9094379171507/100000000000000 : ℝ)^4167
        have hw : |(-729692983/5000000000 : ℝ)|=(729692983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499009803/10000000000 : ℝ)|^5191 ≤ (47474665880147/100000000000000 : ℝ)^4167
        have hw : |(5499009803/10000000000 : ℝ)|=(5499009803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8191599/16000000 : ℝ)|^5191 ≤ (21715477469233/50000000000000 : ℝ)^4167
        have hw : |(8191599/16000000 : ℝ)|=(8191599/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s1_1 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353557201/10000000000 : ℝ)*x 0 + (-66282131/400000000 : ℝ)*x 1 + (5119748871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353557201/10000000000 : ℝ)^5191 ≤ (11478865270911/25000000000000 : ℝ)^4167 := by
    have hnat : (5353557201 : ℕ)^5191*25000000000000^4167 ≤ 11478865270911^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353557201 10000000000 11478865270911 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66282131/400000000 : ℝ)^5191 ≤ (665849330189/6250000000000 : ℝ)^4167 := by
    have hnat : (66282131 : ℕ)^5191*6250000000000^4167 ≤ 665849330189^4167*400000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66282131 400000000 665849330189 6250000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5119748871/10000000000 : ℝ)^5191 ≤ (43430949612373/100000000000000 : ℝ)^4167 := by
    have hnat : (5119748871 : ℕ)^5191*100000000000000^4167 ≤ 43430949612373^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119748871 10000000000 43430949612373 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353557201/10000000000 : ℝ), (-66282131/400000000 : ℝ), (5119748871/10000000000 : ℝ)] ![(11478865270911/25000000000000 : ℝ), (665849330189/6250000000000 : ℝ), (43430949612373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353557201/10000000000 : ℝ)|^5191 ≤ (11478865270911/25000000000000 : ℝ)^4167
        have hw : |(5353557201/10000000000 : ℝ)|=(5353557201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66282131/400000000 : ℝ)|^5191 ≤ (665849330189/6250000000000 : ℝ)^4167
        have hw : |(-66282131/400000000 : ℝ)|=(66282131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5119748871/10000000000 : ℝ)|^5191 ≤ (43430949612373/100000000000000 : ℝ)^4167
        have hw : |(5119748871/10000000000 : ℝ)|=(5119748871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s1_2 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353556161/10000000000 : ℝ)*x 0 + (2559874887/5000000000 : ℝ)*x 1 + (-1657053473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353556161/10000000000 : ℝ)^5191 ≤ (1836617998881/4000000000000 : ℝ)^4167 := by
    have hnat : (5353556161 : ℕ)^5191*4000000000000^4167 ≤ 1836617998881^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353556161 10000000000 1836617998881 4000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559874887/5000000000 : ℝ)^5191 ≤ (10857739788739/25000000000000 : ℝ)^4167 := by
    have hnat : (2559874887 : ℕ)^5191*25000000000000^4167 ≤ 10857739788739^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559874887 5000000000 10857739788739 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1657053473/10000000000 : ℝ)^5191 ≤ (5326795434419/50000000000000 : ℝ)^4167 := by
    have hnat : (1657053473 : ℕ)^5191*50000000000000^4167 ≤ 5326795434419^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657053473 10000000000 5326795434419 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353556161/10000000000 : ℝ), (2559874887/5000000000 : ℝ), (-1657053473/10000000000 : ℝ)] ![(1836617998881/4000000000000 : ℝ), (10857739788739/25000000000000 : ℝ), (5326795434419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353556161/10000000000 : ℝ)|^5191 ≤ (1836617998881/4000000000000 : ℝ)^4167
        have hw : |(5353556161/10000000000 : ℝ)|=(5353556161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559874887/5000000000 : ℝ)|^5191 ≤ (10857739788739/25000000000000 : ℝ)^4167
        have hw : |(2559874887/5000000000 : ℝ)|=(2559874887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1657053473/10000000000 : ℝ)|^5191 ≤ (5326795434419/50000000000000 : ℝ)^4167
        have hw : |(-1657053473/10000000000 : ℝ)|=(1657053473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s1_3 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823863719/2000000000 : ℝ)*x 0 + (451202567/1250000000 : ℝ)*x 1 + (2337067603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823863719/2000000000 : ℝ)^5191 ≤ (6625252523291/20000000000000 : ℝ)^4167 := by
    have hnat : (823863719 : ℕ)^5191*20000000000000^4167 ≤ 6625252523291^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823863719 2000000000 6625252523291 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451202567/1250000000 : ℝ)^5191 ≤ (28100367453049/100000000000000 : ℝ)^4167 := by
    have hnat : (451202567 : ℕ)^5191*100000000000000^4167 ≤ 28100367453049^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451202567 1250000000 28100367453049 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2337067603/5000000000 : ℝ)^5191 ≤ (38773369916499/100000000000000 : ℝ)^4167 := by
    have hnat : (2337067603 : ℕ)^5191*100000000000000^4167 ≤ 38773369916499^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337067603 5000000000 38773369916499 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823863719/2000000000 : ℝ), (451202567/1250000000 : ℝ), (2337067603/5000000000 : ℝ)] ![(6625252523291/20000000000000 : ℝ), (28100367453049/100000000000000 : ℝ), (38773369916499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823863719/2000000000 : ℝ)|^5191 ≤ (6625252523291/20000000000000 : ℝ)^4167
        have hw : |(823863719/2000000000 : ℝ)|=(823863719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451202567/1250000000 : ℝ)|^5191 ≤ (28100367453049/100000000000000 : ℝ)^4167
        have hw : |(451202567/1250000000 : ℝ)|=(451202567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2337067603/5000000000 : ℝ)|^5191 ≤ (38773369916499/100000000000000 : ℝ)^4167
        have hw : |(2337067603/5000000000 : ℝ)|=(2337067603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s1_4 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-182450011/1250000000 : ℝ)*x 0 + (2562168053/5000000000 : ℝ)*x 1 + (343396711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182450011/1250000000 : ℝ)^5191 ≤ (7276833147/80000000000 : ℝ)^4167 := by
    have hnat : (182450011 : ℕ)^5191*80000000000^4167 ≤ 7276833147^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182450011 1250000000 7276833147 80000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562168053/5000000000 : ℝ)^5191 ≤ (10869857804157/25000000000000 : ℝ)^4167 := by
    have hnat : (2562168053 : ℕ)^5191*25000000000000^4167 ≤ 10869857804157^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562168053 5000000000 10869857804157 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343396711/625000000 : ℝ)^5191 ≤ (1896981093341/4000000000000 : ℝ)^4167 := by
    have hnat : (343396711 : ℕ)^5191*4000000000000^4167 ≤ 1896981093341^4167*625000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343396711 625000000 1896981093341 4000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182450011/1250000000 : ℝ), (2562168053/5000000000 : ℝ), (343396711/625000000 : ℝ)] ![(7276833147/80000000000 : ℝ), (10869857804157/25000000000000 : ℝ), (1896981093341/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182450011/1250000000 : ℝ)|^5191 ≤ (7276833147/80000000000 : ℝ)^4167
        have hw : |(-182450011/1250000000 : ℝ)|=(182450011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2562168053/5000000000 : ℝ)|^5191 ≤ (10869857804157/25000000000000 : ℝ)^4167
        have hw : |(2562168053/5000000000 : ℝ)|=(2562168053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(343396711/625000000 : ℝ)|^5191 ≤ (1896981093341/4000000000000 : ℝ)^4167
        have hw : |(343396711/625000000 : ℝ)|=(343396711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s1_5 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252052643/10000000000 : ℝ)*x 0 + (-641226803/5000000000 : ℝ)*x 1 + (2747173799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252052643/10000000000 : ℝ)^5191 ≤ (11208374920029/25000000000000 : ℝ)^4167 := by
    have hnat : (5252052643 : ℕ)^5191*25000000000000^4167 ≤ 11208374920029^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252052643 10000000000 11208374920029 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641226803/5000000000 : ℝ)^5191 ≤ (3870985296491/50000000000000 : ℝ)^4167 := by
    have hnat : (641226803 : ℕ)^5191*50000000000000^4167 ≤ 3870985296491^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641226803 5000000000 3870985296491 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747173799/5000000000 : ℝ)^5191 ≤ (47424529720607/100000000000000 : ℝ)^4167 := by
    have hnat : (2747173799 : ℕ)^5191*100000000000000^4167 ≤ 47424529720607^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747173799 5000000000 47424529720607 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252052643/10000000000 : ℝ), (-641226803/5000000000 : ℝ), (2747173799/5000000000 : ℝ)] ![(11208374920029/25000000000000 : ℝ), (3870985296491/50000000000000 : ℝ), (47424529720607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252052643/10000000000 : ℝ)|^5191 ≤ (11208374920029/25000000000000 : ℝ)^4167
        have hw : |(5252052643/10000000000 : ℝ)|=(5252052643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-641226803/5000000000 : ℝ)|^5191 ≤ (3870985296491/50000000000000 : ℝ)^4167
        have hw : |(-641226803/5000000000 : ℝ)|=(641226803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747173799/5000000000 : ℝ)|^5191 ≤ (47424529720607/100000000000000 : ℝ)^4167
        have hw : |(2747173799/5000000000 : ℝ)|=(2747173799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s1_6 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656506439/1250000000 : ℝ)*x 0 + (1373587239/2500000000 : ℝ)*x 1 + (-1282453263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656506439/1250000000 : ℝ)^5191 ≤ (2241674382647/5000000000000 : ℝ)^4167 := by
    have hnat : (656506439 : ℕ)^5191*5000000000000^4167 ≤ 2241674382647^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656506439 1250000000 2241674382647 5000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373587239/2500000000 : ℝ)^5191 ≤ (4742454432267/10000000000000 : ℝ)^4167 := by
    have hnat : (1373587239 : ℕ)^5191*10000000000000^4167 ≤ 4742454432267^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373587239 2500000000 4742454432267 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282453263/10000000000 : ℝ)^5191 ≤ (3870984006753/50000000000000 : ℝ)^4167 := by
    have hnat : (1282453263 : ℕ)^5191*50000000000000^4167 ≤ 3870984006753^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282453263 10000000000 3870984006753 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656506439/1250000000 : ℝ), (1373587239/2500000000 : ℝ), (-1282453263/10000000000 : ℝ)] ![(2241674382647/5000000000000 : ℝ), (4742454432267/10000000000000 : ℝ), (3870984006753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656506439/1250000000 : ℝ)|^5191 ≤ (2241674382647/5000000000000 : ℝ)^4167
        have hw : |(656506439/1250000000 : ℝ)|=(656506439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373587239/2500000000 : ℝ)|^5191 ≤ (4742454432267/10000000000000 : ℝ)^4167
        have hw : |(1373587239/2500000000 : ℝ)|=(1373587239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1282453263/10000000000 : ℝ)|^5191 ≤ (3870984006753/50000000000000 : ℝ)^4167
        have hw : |(-1282453263/10000000000 : ℝ)|=(1282453263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s1_7 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4119919981/10000000000 : ℝ)*x 0 + (291328989/625000000 : ℝ)*x 1 + (1811352093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119919981/10000000000 : ℝ)^5191 ≤ (828307183003/2500000000000 : ℝ)^4167 := by
    have hnat : (4119919981 : ℕ)^5191*2500000000000^4167 ≤ 828307183003^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119919981 10000000000 828307183003 2500000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291328989/625000000 : ℝ)^5191 ≤ (9660101185027/25000000000000 : ℝ)^4167 := by
    have hnat : (291328989 : ℕ)^5191*25000000000000^4167 ≤ 9660101185027^4167*625000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291328989 625000000 9660101185027 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1811352093/5000000000 : ℝ)^5191 ≤ (14113653960657/50000000000000 : ℝ)^4167 := by
    have hnat : (1811352093 : ℕ)^5191*50000000000000^4167 ≤ 14113653960657^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811352093 5000000000 14113653960657 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119919981/10000000000 : ℝ), (291328989/625000000 : ℝ), (1811352093/5000000000 : ℝ)] ![(828307183003/2500000000000 : ℝ), (9660101185027/25000000000000 : ℝ), (14113653960657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119919981/10000000000 : ℝ)|^5191 ≤ (828307183003/2500000000000 : ℝ)^4167
        have hw : |(4119919981/10000000000 : ℝ)|=(4119919981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291328989/625000000 : ℝ)|^5191 ≤ (9660101185027/25000000000000 : ℝ)^4167
        have hw : |(291328989/625000000 : ℝ)|=(291328989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1811352093/5000000000 : ℝ)|^5191 ≤ (14113653960657/50000000000000 : ℝ)^4167
        have hw : |(1811352093/5000000000 : ℝ)|=(1811352093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1696_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11207/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/160 : ℝ)*pair X i i ≤ pair X i h) :
    (1191/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2201/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11207/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9/160 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11207/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9/160 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11207/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9/160 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11207/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9/160 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11207/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9/160 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11207/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9/160 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9/160 : ℝ) ^ (5183/1024 : ℝ) ≤ (5896928857253/12500000000000000000 : ℝ) := by
    have hpowers : (9/160 : ℝ)^5183 ≤ (5896928857253/12500000000000000000 : ℝ)^1024 := by
      have hnat : (9 : ℕ)^5183*12500000000000000000^1024 ≤ 5896928857253^1024*160^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9 160 5896928857253 12500000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9/160 : ℝ)) (X := (5896928857253/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11207/50000 : ℝ) ^ (5183/1024 : ℝ) ≤ (25799337936641427/50000000000000000000 : ℝ) := by
    have hpowers : (11207/50000 : ℝ)^5183 ≤ (25799337936641427/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11207 : ℕ)^5183*50000000000000000000^1024 ≤ 25799337936641427^1024*50000^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 50000 25799337936641427 50000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/50000 : ℝ)) (X := (25799337936641427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250005896928857253/6250000000000000000 : ℝ) ≤ (2500000466019901/2500000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (6250005896928857253/6250000000000000000 : ℝ)^1024 ≤ (2500000466019901/2500000000000000 : ℝ)^5183 := by
      have hnat : (6250005896928857253 : ℕ)^1024*2500000000000000^5183 ≤ 2500000466019901^5183*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250005896928857253 6250000000000000000 2500000466019901 2500000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000466019901/2500000000000000 : ℝ)) (X := (6250005896928857253/6250000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025822925652070439/50000000000000000000 : ℝ) ≤ (5000510075214153/5000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (50025822925652070439/50000000000000000000 : ℝ)^1024 ≤ (5000510075214153/5000000000000000 : ℝ)^5183 := by
      have hnat : (50025822925652070439 : ℕ)^1024*5000000000000000^5183 ≤ 5000510075214153^5183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025822925652070439 50000000000000000000 5000510075214153 5000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000510075214153/5000000000000000 : ℝ)) (X := (50025822925652070439/50000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25025799337936641427/25000000000000000000 : ℝ) ≤ (625127402298563/625000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (25025799337936641427/25000000000000000000 : ℝ)^1024 ≤ (625127402298563/625000000000000 : ℝ)^5183 := by
      have hnat : (25025799337936641427 : ℕ)^1024*625000000000000^5183 ≤ 625127402298563^5183*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025799337936641427 25000000000000000000 625127402298563 625000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625127402298563/625000000000000 : ℝ)) (X := (25025799337936641427/25000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5896928857253/12500000000000000000 : ℝ) ≤ ((20984821946826196757/20986250000000000000 : ℝ)+2*(509143174351/839450000000000 : ℝ)*(9/160 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (20984821946826196757/20986250000000000000 : ℝ)+2*(509143174351/839450000000000 : ℝ)*(9/160 : ℝ)=(2500000466019901/2500000000000000 : ℝ) by norm_num, show 1+2*(5896928857253/12500000000000000000 : ℝ)=(6250005896928857253/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25799337936641427/50000000000000000000 : ℝ)+(5896928857253/12500000000000000000 : ℝ) ≤ ((20984821946826196757/20986250000000000000 : ℝ)+(509143174351/839450000000000 : ℝ)*((11207/50000 : ℝ)+(9/160 : ℝ)))^(5183/1024 : ℝ) := by
    rw [show (20984821946826196757/20986250000000000000 : ℝ)+(509143174351/839450000000000 : ℝ)*((11207/50000 : ℝ)+(9/160 : ℝ))=(5000510075214153/5000000000000000 : ℝ) by norm_num, show 1+(25799337936641427/50000000000000000000 : ℝ)+(5896928857253/12500000000000000000 : ℝ)=(50025822925652070439/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25799337936641427/50000000000000000000 : ℝ) ≤ ((20984821946826196757/20986250000000000000 : ℝ)+2*(509143174351/839450000000000 : ℝ)*(11207/50000 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (20984821946826196757/20986250000000000000 : ℝ)+2*(509143174351/839450000000000 : ℝ)*(11207/50000 : ℝ)=(625127402298563/625000000000000 : ℝ) by norm_num, show 1+2*(25799337936641427/50000000000000000000 : ℝ)=(25025799337936641427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20984821946826196757/20986250000000000000 : ℝ)*(X 1 0+X 2 0)+(509143174351/839450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9/160 : ℝ)) (hi := (11207/50000 : ℝ)) (c := (20984821946826196757/20986250000000000000 : ℝ)) (alpha := (509143174351/839450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20984821946826196757/20986250000000000000 : ℝ)*(X 0 1+X 2 1)+(509143174351/839450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9/160 : ℝ)) (hi := (11207/50000 : ℝ)) (c := (20984821946826196757/20986250000000000000 : ℝ)) (alpha := (509143174351/839450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20984821946826196757/20986250000000000000 : ℝ)*(X 0 2+X 1 2)+(509143174351/839450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9/160 : ℝ)) (hi := (11207/50000 : ℝ)) (c := (20984821946826196757/20986250000000000000 : ℝ)) (alpha := (509143174351/839450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-729692983/5000000000 : ℝ)*X 0 0+(5499009803/10000000000 : ℝ)*X 0 1+(8191599/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353557201/10000000000 : ℝ)*X 1 0+(-66282131/400000000 : ℝ)*X 1 1+(5119748871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353556161/10000000000 : ℝ)*X 2 0+(2559874887/5000000000 : ℝ)*X 2 1+(-1657053473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((823863719/2000000000 : ℝ)*X 0 0+(451202567/1250000000 : ℝ)*X 0 1+(2337067603/5000000000 : ℝ)*X 0 2+(823863719/2000000000 : ℝ)*X 1 0+(451202567/1250000000 : ℝ)*X 1 1+(2337067603/5000000000 : ℝ)*X 1 2+(823863719/2000000000 : ℝ)*X 2 0+(451202567/1250000000 : ℝ)*X 2 1+(2337067603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-182450011/1250000000 : ℝ)*X 0 0+(2562168053/5000000000 : ℝ)*X 0 1+(343396711/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252052643/10000000000 : ℝ)*X 1 0+(-641226803/5000000000 : ℝ)*X 1 1+(2747173799/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((656506439/1250000000 : ℝ)*X 2 0+(1373587239/2500000000 : ℝ)*X 2 1+(-1282453263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4119919981/10000000000 : ℝ)*X 0 0+(291328989/625000000 : ℝ)*X 0 1+(1811352093/5000000000 : ℝ)*X 0 2+(4119919981/10000000000 : ℝ)*X 1 0+(291328989/625000000 : ℝ)*X 1 1+(1811352093/5000000000 : ℝ)*X 1 2+(4119919981/10000000000 : ℝ)*X 2 0+(291328989/625000000 : ℝ)*X 2 1+(1811352093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (223686396255293104717636851/16395507812500000000000000000000 : ℝ) := by norm_num
    linear_combination (2002858063/100000000000000 : ℝ)*(base19) + (90496793/6250000000000 : ℝ)*(base23) + (5713237/25000000000000 : ℝ)*(lower2) + (356760013/100000000000000 : ℝ)*(upper3) + (16306151/12500000000000 : ℝ)*(upper5) + (894037047398929/50000000000000 : ℝ)*(major0) + (894037047398929/50000000000000 : ℝ)*(major1) + (894037047398929/50000000000000 : ℝ)*(major2) + (65918210836399/2500000000000 : ℝ)*(sp0) + (527347890475443/20000000000000 : ℝ)*(sp1) + (263674000728659/10000000000000 : ℝ)*(sp2) + (939400294430989/100000000000000 : ℝ)*(sp3) + (6510889659/50000000000000 : ℝ)*(sp4) + (5985157727/100000000000000 : ℝ)*(sp7) + (234851569897179/25000000000000 : ℝ)*(f.failure) + (1318370727617639/50000000000000 : ℝ)*(f.sum) + (107492847353/41972500000000000000000000000 : ℝ)*base65 + (1771823167123298253/1049312500000000000000000000000000 : ℝ)*base67 + (5918445114962298253/1049312500000000000000000000000000 : ℝ)*base69 + (2138932114458764247/1049312500000000000000000000000000 : ℝ)*base72 + (168840399991199/83945000000000000000000000000 : ℝ)*base74 + (8271025044153985753/1049312500000000000000000000000000 : ℝ)*base75 + (5357770050761548253/1049312500000000000000000000000000 : ℝ)*base77 + (5228784172135298253/1049312500000000000000000000000000 : ℝ)*base79 + (77073700592523/41972500000000000000000000000 : ℝ)*base81 + (18697091/2500000000000000000000 : ℝ)*base90 + (18697091/2500000000000000000000 : ℝ)*base92 + (18697091/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8351776268288745694947009/3218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281663019/25000000000000 : ℝ)*(base19) + (296978507/50000000000000 : ℝ)*(base23) + (5670479/100000000000000 : ℝ)*(upper3) + (1205563/25000000000000 : ℝ)*(lower4) + (366549564542871/20000000000000 : ℝ)*(major0) + (366549564542871/20000000000000 : ℝ)*(major1) + (458186955678589/25000000000000 : ℝ)*(major2) + (1875199659/12500000000000 : ℝ)*(sp1) + (17077314073/100000000000000 : ℝ)*(sp2) + (2526418589/100000000000000 : ℝ)*(sp3) + (13513094490973/500000000000 : ℝ)*(sp4) + (675650692486313/25000000000000 : ℝ)*(sp5) + (337825153365439/12500000000000 : ℝ)*(sp6) + (962874134324629/100000000000000 : ℝ)*(sp7) + (481438330371609/50000000000000 : ℝ)*(f.failure) + (13513094490973/500000000000 : ℝ)*(f.sum) + (430200384710719/83945000000000000000000000000 : ℝ)*base66 + (2570702424912550653/419725000000000000000000000000000 : ℝ)*base68 + (184839388576417123/524656250000000000000000000000000 : ℝ)*base69 + (5319161876334250653/419725000000000000000000000000000 : ℝ)*base72 + (127164876673599/83945000000000000000000000000 : ℝ)*base74 + (1869502733285417123/524656250000000000000000000000000 : ℝ)*base75 + (1711924508609030653/419725000000000000000000000000000 : ℝ)*base78 + (904251709136455653/419725000000000000000000000000000 : ℝ)*base80 + (10274197468277/3357800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (60731439/5000000000000000000000 : ℝ)*base89 + (60731439/5000000000000000000000 : ℝ)*base91 + (10731439/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1696_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11207/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/160 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2201/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1696_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1696_s2_0 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73204163/500000000 : ℝ)*x 0 + (2740019923/5000000000 : ℝ)*x 1 + (5135589197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73204163/500000000 : ℝ)^5191 ≤ (4565429372211/50000000000000 : ℝ)^4167 := by
    have hnat : (73204163 : ℕ)^5191*50000000000000^4167 ≤ 4565429372211^4167*500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73204163 500000000 4565429372211 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740019923/5000000000 : ℝ)^5191 ≤ (47270733111039/100000000000000 : ℝ)^4167 := by
    have hnat : (2740019923 : ℕ)^5191*100000000000000^4167 ≤ 47270733111039^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740019923 5000000000 47270733111039 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135589197/10000000000 : ℝ)^5191 ≤ (43598408132983/100000000000000 : ℝ)^4167 := by
    have hnat : (5135589197 : ℕ)^5191*100000000000000^4167 ≤ 43598408132983^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135589197 10000000000 43598408132983 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73204163/500000000 : ℝ), (2740019923/5000000000 : ℝ), (5135589197/10000000000 : ℝ)] ![(4565429372211/50000000000000 : ℝ), (47270733111039/100000000000000 : ℝ), (43598408132983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73204163/500000000 : ℝ)|^5191 ≤ (4565429372211/50000000000000 : ℝ)^4167
        have hw : |(-73204163/500000000 : ℝ)|=(73204163/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740019923/5000000000 : ℝ)|^5191 ≤ (47270733111039/100000000000000 : ℝ)^4167
        have hw : |(2740019923/5000000000 : ℝ)|=(2740019923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135589197/10000000000 : ℝ)|^5191 ≤ (43598408132983/100000000000000 : ℝ)^4167
        have hw : |(5135589197/10000000000 : ℝ)|=(5135589197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s2_1 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348453467/10000000000 : ℝ)*x 0 + (-821468871/5000000000 : ℝ)*x 1 + (1027117833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348453467/10000000000 : ℝ)^5191 ≤ (45860937903909/100000000000000 : ℝ)^4167 := by
    have hnat : (5348453467 : ℕ)^5191*100000000000000^4167 ≤ 45860937903909^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348453467 10000000000 45860937903909 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (821468871/5000000000 : ℝ)^5191 ≤ (10540654294543/100000000000000 : ℝ)^4167 := by
    have hnat : (821468871 : ℕ)^5191*100000000000000^4167 ≤ 10540654294543^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821468871 5000000000 10540654294543 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027117833/2000000000 : ℝ)^5191 ≤ (43598407794561/100000000000000 : ℝ)^4167 := by
    have hnat : (1027117833 : ℕ)^5191*100000000000000^4167 ≤ 43598407794561^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027117833 2000000000 43598407794561 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348453467/10000000000 : ℝ), (-821468871/5000000000 : ℝ), (1027117833/2000000000 : ℝ)] ![(45860937903909/100000000000000 : ℝ), (10540654294543/100000000000000 : ℝ), (43598407794561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348453467/10000000000 : ℝ)|^5191 ≤ (45860937903909/100000000000000 : ℝ)^4167
        have hw : |(5348453467/10000000000 : ℝ)|=(5348453467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-821468871/5000000000 : ℝ)|^5191 ≤ (10540654294543/100000000000000 : ℝ)^4167
        have hw : |(-821468871/5000000000 : ℝ)|=(821468871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027117833/2000000000 : ℝ)|^5191 ≤ (43598407794561/100000000000000 : ℝ)^4167
        have hw : |(1027117833/2000000000 : ℝ)|=(1027117833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s2_2 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267422691/500000000 : ℝ)*x 0 + (2567794591/5000000000 : ℝ)*x 1 + (-1642937247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267422691/500000000 : ℝ)^5191 ≤ (9172188334913/20000000000000 : ℝ)^4167 := by
    have hnat : (267422691 : ℕ)^5191*20000000000000^4167 ≤ 9172188334913^4167*500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267422691 500000000 9172188334913 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567794591/5000000000 : ℝ)^5191 ≤ (10899601993587/25000000000000 : ℝ)^4167 := by
    have hnat : (2567794591 : ℕ)^5191*25000000000000^4167 ≤ 10899601993587^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567794591 5000000000 10899601993587 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1642937247/10000000000 : ℝ)^5191 ≤ (5270325169167/50000000000000 : ℝ)^4167 := by
    have hnat : (1642937247 : ℕ)^5191*50000000000000^4167 ≤ 5270325169167^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642937247 10000000000 5270325169167 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267422691/500000000 : ℝ), (2567794591/5000000000 : ℝ), (-1642937247/10000000000 : ℝ)] ![(9172188334913/20000000000000 : ℝ), (10899601993587/25000000000000 : ℝ), (5270325169167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267422691/500000000 : ℝ)|^5191 ≤ (9172188334913/20000000000000 : ℝ)^4167
        have hw : |(267422691/500000000 : ℝ)|=(267422691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567794591/5000000000 : ℝ)|^5191 ≤ (10899601993587/25000000000000 : ℝ)^4167
        have hw : |(2567794591/5000000000 : ℝ)|=(2567794591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1642937247/10000000000 : ℝ)|^5191 ≤ (5270325169167/50000000000000 : ℝ)^4167
        have hw : |(-1642937247/10000000000 : ℝ)|=(1642937247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s2_3 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4122939663/10000000000 : ℝ)*x 0 + (365814179/1000000000 : ℝ)*x 1 + (2312475121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4122939663/10000000000 : ℝ)^5191 ≤ (265300334839/800000000000 : ℝ)^4167 := by
    have hnat : (4122939663 : ℕ)^5191*800000000000^4167 ≤ 265300334839^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122939663 10000000000 265300334839 800000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365814179/1000000000 : ℝ)^5191 ≤ (89286551877/312500000000 : ℝ)^4167 := by
    have hnat : (365814179 : ℕ)^5191*312500000000^4167 ≤ 89286551877^4167*1000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365814179 1000000000 89286551877 312500000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2312475121/5000000000 : ℝ)^5191 ≤ (1913288076387/5000000000000 : ℝ)^4167 := by
    have hnat : (2312475121 : ℕ)^5191*5000000000000^4167 ≤ 1913288076387^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312475121 5000000000 1913288076387 5000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4122939663/10000000000 : ℝ), (365814179/1000000000 : ℝ), (2312475121/5000000000 : ℝ)] ![(265300334839/800000000000 : ℝ), (89286551877/312500000000 : ℝ), (1913288076387/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4122939663/10000000000 : ℝ)|^5191 ≤ (265300334839/800000000000 : ℝ)^4167
        have hw : |(4122939663/10000000000 : ℝ)|=(4122939663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(365814179/1000000000 : ℝ)|^5191 ≤ (89286551877/312500000000 : ℝ)^4167
        have hw : |(365814179/1000000000 : ℝ)|=(365814179/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2312475121/5000000000 : ℝ)|^5191 ≤ (1913288076387/5000000000000 : ℝ)^4167
        have hw : |(2312475121/5000000000 : ℝ)|=(2312475121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s2_4 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45757621/312500000 : ℝ)*x 0 + (2569687503/5000000000 : ℝ)*x 1 + (136904929/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45757621/312500000 : ℝ)^5191 ≤ (913210657959/10000000000000 : ℝ)^4167 := by
    have hnat : (45757621 : ℕ)^5191*10000000000000^4167 ≤ 913210657959^4167*312500000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45757621 312500000 913210657959 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569687503/5000000000 : ℝ)^5191 ≤ (21819224612419/50000000000000 : ℝ)^4167 := by
    have hnat : (2569687503 : ℕ)^5191*50000000000000^4167 ≤ 21819224612419^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569687503 5000000000 21819224612419 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136904929/250000000 : ℝ)^5191 ≤ (47229444181673/100000000000000 : ℝ)^4167 := by
    have hnat : (136904929 : ℕ)^5191*100000000000000^4167 ≤ 47229444181673^4167*250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136904929 250000000 47229444181673 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45757621/312500000 : ℝ), (2569687503/5000000000 : ℝ), (136904929/250000000 : ℝ)] ![(913210657959/10000000000000 : ℝ), (21819224612419/50000000000000 : ℝ), (47229444181673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45757621/312500000 : ℝ)|^5191 ≤ (913210657959/10000000000000 : ℝ)^4167
        have hw : |(-45757621/312500000 : ℝ)|=(45757621/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569687503/5000000000 : ℝ)|^5191 ≤ (21819224612419/50000000000000 : ℝ)^4167
        have hw : |(2569687503/5000000000 : ℝ)|=(2569687503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136904929/250000000 : ℝ)|^5191 ≤ (47229444181673/100000000000000 : ℝ)^4167
        have hw : |(136904929/250000000 : ℝ)|=(136904929/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s2_5 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256314599/10000000000 : ℝ)*x 0 + (-20348901/156250000 : ℝ)*x 1 + (684524653/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256314599/10000000000 : ℝ)^5191 ≤ (4487882630189/10000000000000 : ℝ)^4167 := by
    have hnat : (5256314599 : ℕ)^5191*10000000000000^4167 ≤ 4487882630189^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256314599 10000000000 4487882630189 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20348901/156250000 : ℝ)^5191 ≤ (7891728817727/100000000000000 : ℝ)^4167 := by
    have hnat : (20348901 : ℕ)^5191*100000000000000^4167 ≤ 7891728817727^4167*156250000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20348901 156250000 7891728817727 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684524653/1250000000 : ℝ)^5191 ≤ (47229444869281/100000000000000 : ℝ)^4167 := by
    have hnat : (684524653 : ℕ)^5191*100000000000000^4167 ≤ 47229444869281^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684524653 1250000000 47229444869281 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256314599/10000000000 : ℝ), (-20348901/156250000 : ℝ), (684524653/1250000000 : ℝ)] ![(4487882630189/10000000000000 : ℝ), (7891728817727/100000000000000 : ℝ), (47229444869281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256314599/10000000000 : ℝ)|^5191 ≤ (4487882630189/10000000000000 : ℝ)^4167
        have hw : |(5256314599/10000000000 : ℝ)|=(5256314599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20348901/156250000 : ℝ)|^5191 ≤ (7891728817727/100000000000000 : ℝ)^4167
        have hw : |(-20348901/156250000 : ℝ)|=(20348901/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684524653/1250000000 : ℝ)|^5191 ≤ (47229444869281/100000000000000 : ℝ)^4167
        have hw : |(684524653/1250000000 : ℝ)|=(684524653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s2_6 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628157301/5000000000 : ℝ)*x 0 + (1095239447/2000000000 : ℝ)*x 1 + (-325582411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628157301/5000000000 : ℝ)^5191 ≤ (22439413166899/50000000000000 : ℝ)^4167 := by
    have hnat : (2628157301 : ℕ)^5191*50000000000000^4167 ≤ 22439413166899^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628157301 5000000000 22439413166899 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095239447/2000000000 : ℝ)^5191 ≤ (5903680623433/12500000000000 : ℝ)^4167 := by
    have hnat : (1095239447 : ℕ)^5191*12500000000000^4167 ≤ 5903680623433^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095239447 2000000000 5903680623433 12500000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325582411/2500000000 : ℝ)^5191 ≤ (7891728666751/100000000000000 : ℝ)^4167 := by
    have hnat : (325582411 : ℕ)^5191*100000000000000^4167 ≤ 7891728666751^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325582411 2500000000 7891728666751 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628157301/5000000000 : ℝ), (1095239447/2000000000 : ℝ), (-325582411/2500000000 : ℝ)] ![(22439413166899/50000000000000 : ℝ), (5903680623433/12500000000000 : ℝ), (7891728666751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628157301/5000000000 : ℝ)|^5191 ≤ (22439413166899/50000000000000 : ℝ)^4167
        have hw : |(2628157301/5000000000 : ℝ)|=(2628157301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095239447/2000000000 : ℝ)|^5191 ≤ (5903680623433/12500000000000 : ℝ)^4167
        have hw : |(1095239447/2000000000 : ℝ)|=(1095239447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325582411/2500000000 : ℝ)|^5191 ≤ (7891728666751/100000000000000 : ℝ)^4167
        have hw : |(-325582411/2500000000 : ℝ)|=(325582411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s2_7 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (824678071/2000000000 : ℝ)*x 0 + (922864937/2000000000 : ℝ)*x 1 + (3668926447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824678071/2000000000 : ℝ)^5191 ≤ (33167057856011/100000000000000 : ℝ)^4167 := by
    have hnat : (824678071 : ℕ)^5191*100000000000000^4167 ≤ 33167057856011^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824678071 2000000000 33167057856011 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922864937/2000000000 : ℝ)^5191 ≤ (38156275211/100000000000 : ℝ)^4167 := by
    have hnat : (922864937 : ℕ)^5191*100000000000^4167 ≤ 38156275211^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922864937 2000000000 38156275211 100000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3668926447/10000000000 : ℝ)^5191 ≤ (28676666923507/100000000000000 : ℝ)^4167 := by
    have hnat : (3668926447 : ℕ)^5191*100000000000000^4167 ≤ 28676666923507^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668926447 10000000000 28676666923507 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(824678071/2000000000 : ℝ), (922864937/2000000000 : ℝ), (3668926447/10000000000 : ℝ)] ![(33167057856011/100000000000000 : ℝ), (38156275211/100000000000 : ℝ), (28676666923507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(824678071/2000000000 : ℝ)|^5191 ≤ (33167057856011/100000000000000 : ℝ)^4167
        have hw : |(824678071/2000000000 : ℝ)|=(824678071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922864937/2000000000 : ℝ)|^5191 ≤ (38156275211/100000000000 : ℝ)^4167
        have hw : |(922864937/2000000000 : ℝ)|=(922864937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3668926447/10000000000 : ℝ)|^5191 ≤ (28676666923507/100000000000000 : ℝ)^4167
        have hw : |(3668926447/10000000000 : ℝ)|=(3668926447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1696_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2201/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9873/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17211/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2201/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1191/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2201/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1191/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2201/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1191/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2201/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1191/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2201/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1191/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2201/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1191/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1191/12500 : ℝ) ^ (5183/1024 : ℝ) ≤ (339753097301281/50000000000000000000 : ℝ) := by
    have hpowers : (1191/12500 : ℝ)^5183 ≤ (339753097301281/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1191 : ℕ)^5183*50000000000000000000^1024 ≤ 339753097301281^1024*12500^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1191 12500 339753097301281 50000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1191/12500 : ℝ)) (X := (339753097301281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2201/12500 : ℝ) ^ (5183/1024 : ℝ) ≤ (15210505093946727/100000000000000000000 : ℝ) := by
    have hpowers : (2201/12500 : ℝ)^5183 ≤ (15210505093946727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2201 : ℕ)^5183*100000000000000000000^1024 ≤ 15210505093946727^1024*12500^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 12500 15210505093946727 100000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/12500 : ℝ)) (X := (15210505093946727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000339753097301281/25000000000000000000 : ℝ) ≤ (10000026849722143/10000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (25000339753097301281/25000000000000000000 : ℝ)^1024 ≤ (10000026849722143/10000000000000000 : ℝ)^5183 := by
      have hnat : (25000339753097301281 : ℕ)^1024*10000000000000000^5183 ≤ 10000026849722143^5183*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000339753097301281 25000000000000000000 10000026849722143 10000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000026849722143/10000000000000000 : ℝ)) (X := (25000339753097301281/25000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015890011288549289/100000000000000000000 : ℝ) ≤ (625019619832031/625000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (100015890011288549289/100000000000000000000 : ℝ)^1024 ≤ (625019619832031/625000000000000 : ℝ)^5183 := by
      have hnat : (100015890011288549289 : ℕ)^1024*625000000000000^5183 ≤ 625019619832031^5183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015890011288549289 100000000000000000000 625019619832031 625000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625019619832031/625000000000000 : ℝ)) (X := (100015890011288549289/100000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015210505093946727/50000000000000000000 : ℝ) ≤ (10000600984902849/10000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (50015210505093946727/50000000000000000000 : ℝ)^1024 ≤ (10000600984902849/10000000000000000 : ℝ)^5183 := by
      have hnat : (50015210505093946727 : ℕ)^1024*10000000000000000^5183 ≤ 10000600984902849^5183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015210505093946727 50000000000000000000 10000600984902849 10000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000600984902849/10000000000000000 : ℝ)) (X := (50015210505093946727/50000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(339753097301281/50000000000000000000 : ℝ) ≤ ((315604478850598237/315625000000000000 : ℝ)+2*(287067590353/808000000000000 : ℝ)*(1191/12500 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (315604478850598237/315625000000000000 : ℝ)+2*(287067590353/808000000000000 : ℝ)*(1191/12500 : ℝ)=(10000026849722143/10000000000000000 : ℝ) by norm_num, show 1+2*(339753097301281/50000000000000000000 : ℝ)=(25000339753097301281/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15210505093946727/100000000000000000000 : ℝ)+(339753097301281/50000000000000000000 : ℝ) ≤ ((315604478850598237/315625000000000000 : ℝ)+(287067590353/808000000000000 : ℝ)*((2201/12500 : ℝ)+(1191/12500 : ℝ)))^(5183/1024 : ℝ) := by
    rw [show (315604478850598237/315625000000000000 : ℝ)+(287067590353/808000000000000 : ℝ)*((2201/12500 : ℝ)+(1191/12500 : ℝ))=(625019619832031/625000000000000 : ℝ) by norm_num, show 1+(15210505093946727/100000000000000000000 : ℝ)+(339753097301281/50000000000000000000 : ℝ)=(100015890011288549289/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15210505093946727/100000000000000000000 : ℝ) ≤ ((315604478850598237/315625000000000000 : ℝ)+2*(287067590353/808000000000000 : ℝ)*(2201/12500 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (315604478850598237/315625000000000000 : ℝ)+2*(287067590353/808000000000000 : ℝ)*(2201/12500 : ℝ)=(10000600984902849/10000000000000000 : ℝ) by norm_num, show 1+2*(15210505093946727/100000000000000000000 : ℝ)=(50015210505093946727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (315604478850598237/315625000000000000 : ℝ)*(X 1 0+X 2 0)+(287067590353/808000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (1191/12500 : ℝ)) (hi := (2201/12500 : ℝ)) (c := (315604478850598237/315625000000000000 : ℝ)) (alpha := (287067590353/808000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (315604478850598237/315625000000000000 : ℝ)*(X 0 1+X 2 1)+(287067590353/808000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (1191/12500 : ℝ)) (hi := (2201/12500 : ℝ)) (c := (315604478850598237/315625000000000000 : ℝ)) (alpha := (287067590353/808000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (315604478850598237/315625000000000000 : ℝ)*(X 0 2+X 1 2)+(287067590353/808000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (1191/12500 : ℝ)) (hi := (2201/12500 : ℝ)) (c := (315604478850598237/315625000000000000 : ℝ)) (alpha := (287067590353/808000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-73204163/500000000 : ℝ)*X 0 0+(2740019923/5000000000 : ℝ)*X 0 1+(5135589197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348453467/10000000000 : ℝ)*X 1 0+(-821468871/5000000000 : ℝ)*X 1 1+(1027117833/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267422691/500000000 : ℝ)*X 2 0+(2567794591/5000000000 : ℝ)*X 2 1+(-1642937247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4122939663/10000000000 : ℝ)*X 0 0+(365814179/1000000000 : ℝ)*X 0 1+(2312475121/5000000000 : ℝ)*X 0 2+(4122939663/10000000000 : ℝ)*X 1 0+(365814179/1000000000 : ℝ)*X 1 1+(2312475121/5000000000 : ℝ)*X 1 2+(4122939663/10000000000 : ℝ)*X 2 0+(365814179/1000000000 : ℝ)*X 2 1+(2312475121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-45757621/312500000 : ℝ)*X 0 0+(2569687503/5000000000 : ℝ)*X 0 1+(136904929/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256314599/10000000000 : ℝ)*X 1 0+(-20348901/156250000 : ℝ)*X 1 1+(684524653/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628157301/5000000000 : ℝ)*X 2 0+(1095239447/2000000000 : ℝ)*X 2 1+(-325582411/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((824678071/2000000000 : ℝ)*X 0 0+(922864937/2000000000 : ℝ)*X 0 1+(3668926447/10000000000 : ℝ)*X 0 2+(824678071/2000000000 : ℝ)*X 1 0+(922864937/2000000000 : ℝ)*X 1 1+(3668926447/10000000000 : ℝ)*X 1 2+(824678071/2000000000 : ℝ)*X 2 0+(922864937/2000000000 : ℝ)*X 2 1+(3668926447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (215260102491262118232037683/25250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1207942789/100000000000000 : ℝ)*(base19) + (1256213883/100000000000000 : ℝ)*(base23) + (76665327/100000000000000 : ℝ)*(lower2) + (7965599/25000000000000 : ℝ)*(upper3) + (259263241/100000000000000 : ℝ)*(upper5) + (1968769201003169/100000000000000 : ℝ)*(major0) + (1968769201003169/100000000000000 : ℝ)*(major1) + (196876920100317/10000000000000 : ℝ)*(major2) + (725795855463703/25000000000000 : ℝ)*(sp0) + (1451599128500193/50000000000000 : ℝ)*(sp1) + (725799552182323/25000000000000 : ℝ)*(sp2) + (1034335204400821/100000000000000 : ℝ)*(sp3) + (4010772091/25000000000000 : ℝ)*(sp4) + (689698117/20000000000000 : ℝ)*(sp7) + (517169326445703/50000000000000 : ℝ)*(f.failure) + (116127978597727/4000000000000 : ℝ)*(f.sum) + (79553571128333/80800000000000000000000000000 : ℝ)*base66 + (383775153427794663/126250000000000000000000000000000 : ℝ)*base68 + (54540044580868689/50500000000000000000000000000000 : ℝ)*base69 + (110739304314044663/126250000000000000000000000000000 : ℝ)*base72 + (203956383485267/80800000000000000000000000000 : ℝ)*base73 + (308711317537868689/50500000000000000000000000000000 : ℝ)*base75 + (378256867707057549/252500000000000000000000000000000 : ℝ)*base77 + (245630479904557549/252500000000000000000000000000000 : ℝ)*base79 + (60620979712543/40400000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6772687/5000000000000000000000 : ℝ)*base90 + (6772687/5000000000000000000000 : ℝ)*base92 + (56772687/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255355061642003460254796759/31562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (514502717/50000000000000 : ℝ)*(base19) + (586360977/50000000000000 : ℝ)*(base23) + (85058053/50000000000000 : ℝ)*(upper3) + (7889673/12500000000000 : ℝ)*(lower4) + (172118923/100000000000000 : ℝ)*(upper5) + (1006670127532089/50000000000000 : ℝ)*(major0) + (1006670127532089/50000000000000 : ℝ)*(major1) + (1006670127532089/50000000000000 : ℝ)*(major2) + (4615081329/50000000000000 : ℝ)*(sp1) + (5240957071/50000000000000 : ℝ)*(sp2) + (14844625742483/500000000000 : ℝ)*(sp4) + (742228722332127/25000000000000 : ℝ)*(sp5) + (371114186732563/12500000000000 : ℝ)*(sp6) + (1057755091949841/100000000000000 : ℝ)*(sp7) + (1057755091949841/100000000000000 : ℝ)*(f.failure) + (14844625742483/500000000000 : ℝ)*(f.sum) + (22407122433583/20200000000000000000000000000 : ℝ)*base66 + (66098732337794869/126250000000000000000000000000000 : ℝ)*base67 + (27024831785294869/126250000000000000000000000000000 : ℝ)*base69 + (519941923277794869/126250000000000000000000000000000 : ℝ)*base71 + (52934921509983/20200000000000000000000000000 : ℝ)*base74 + (118971471417205131/126250000000000000000000000000000 : ℝ)*base76 + (121386041690294869/126250000000000000000000000000000 : ℝ)*base77 + (94559276517205131/126250000000000000000000000000000 : ℝ)*base80 + (70365334657983/20200000000000000000000000000 : ℝ)*base82 + (24251511/10000000000000000000000 : ℝ)*base89 + (24251511/10000000000000000000000 : ℝ)*base91 + (24251511/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1696_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2201/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9873/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1696_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1696_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9873/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1696_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1696_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1696_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9873/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1696_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
