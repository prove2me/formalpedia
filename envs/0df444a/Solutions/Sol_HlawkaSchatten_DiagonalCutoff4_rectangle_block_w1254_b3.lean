-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:24:47.266839+00:00
-- url     : https://prove2.me/submissions/5f2efbdb-18fd-404b-8efd-0193b6f959c9

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
theorem support_rectangle_w1254_s9_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114454819/10000000000 : ℝ)*x 0 + (5390925087/10000000000 : ℝ)*x 1 + (2633708971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114454819/10000000000 : ℝ)^8447 ≤ (12859620593283/100000000000000 : ℝ)^6399 := by
    have hnat : (2114454819 : ℕ)^8447*100000000000000^6399 ≤ 12859620593283^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114454819 10000000000 12859620593283 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390925087/10000000000 : ℝ)^8447 ≤ (44236640027223/100000000000000 : ℝ)^6399 := by
    have hnat : (5390925087 : ℕ)^8447*100000000000000^6399 ≤ 44236640027223^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390925087 10000000000 44236640027223 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633708971/5000000000 : ℝ)^8447 ≤ (4290373935913/10000000000000 : ℝ)^6399 := by
    have hnat : (2633708971 : ℕ)^8447*10000000000000^6399 ≤ 4290373935913^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633708971 5000000000 4290373935913 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114454819/10000000000 : ℝ), (5390925087/10000000000 : ℝ), (2633708971/5000000000 : ℝ)] ![(12859620593283/100000000000000 : ℝ), (44236640027223/100000000000000 : ℝ), (4290373935913/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114454819/10000000000 : ℝ)|^8447 ≤ (12859620593283/100000000000000 : ℝ)^6399
        have hw : |(-2114454819/10000000000 : ℝ)|=(2114454819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390925087/10000000000 : ℝ)|^8447 ≤ (44236640027223/100000000000000 : ℝ)^6399
        have hw : |(5390925087/10000000000 : ℝ)|=(5390925087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633708971/5000000000 : ℝ)|^8447 ≤ (4290373935913/10000000000000 : ℝ)^6399
        have hw : |(2633708971/5000000000 : ℝ)|=(2633708971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s9_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668029/1250000 : ℝ)*x 0 + (-217707271/1000000000 : ℝ)*x 1 + (5267417943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668029/1250000 : ℝ)^8447 ≤ (8746312452301/20000000000000 : ℝ)^6399 := by
    have hnat : (668029 : ℕ)^8447*20000000000000^6399 ≤ 8746312452301^6399*1250000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668029 1250000 8746312452301 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217707271/1000000000 : ℝ)^8447 ≤ (6682349179563/50000000000000 : ℝ)^6399 := by
    have hnat : (217707271 : ℕ)^8447*50000000000000^6399 ≤ 6682349179563^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217707271 1000000000 6682349179563 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267417943/10000000000 : ℝ)^8447 ≤ (42903739369881/100000000000000 : ℝ)^6399 := by
    have hnat : (5267417943 : ℕ)^8447*100000000000000^6399 ≤ 42903739369881^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267417943 10000000000 42903739369881 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668029/1250000 : ℝ), (-217707271/1000000000 : ℝ), (5267417943/10000000000 : ℝ)] ![(8746312452301/20000000000000 : ℝ), (6682349179563/50000000000000 : ℝ), (42903739369881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668029/1250000 : ℝ)|^8447 ≤ (8746312452301/20000000000000 : ℝ)^6399
        have hw : |(668029/1250000 : ℝ)|=(668029/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217707271/1000000000 : ℝ)|^8447 ≤ (6682349179563/50000000000000 : ℝ)^6399
        have hw : |(-217707271/1000000000 : ℝ)|=(217707271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267417943/10000000000 : ℝ)|^8447 ≤ (42903739369881/100000000000000 : ℝ)^6399
        have hw : |(5267417943/10000000000 : ℝ)|=(5267417943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s9_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344231999/10000000000 : ℝ)*x 0 + (5267417939/10000000000 : ℝ)*x 1 + (-435414543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344231999/10000000000 : ℝ)^8447 ≤ (43731562250703/100000000000000 : ℝ)^6399 := by
    have hnat : (5344231999 : ℕ)^8447*100000000000000^6399 ≤ 43731562250703^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344231999 10000000000 43731562250703 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267417939/10000000000 : ℝ)^8447 ≤ (21451869663437/50000000000000 : ℝ)^6399 := by
    have hnat : (5267417939 : ℕ)^8447*50000000000000^6399 ≤ 21451869663437^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267417939 10000000000 21451869663437 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435414543/2000000000 : ℝ)^8447 ≤ (3341174599911/25000000000000 : ℝ)^6399 := by
    have hnat : (435414543 : ℕ)^8447*25000000000000^6399 ≤ 3341174599911^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435414543 2000000000 3341174599911 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344231999/10000000000 : ℝ), (5267417939/10000000000 : ℝ), (-435414543/2000000000 : ℝ)] ![(43731562250703/100000000000000 : ℝ), (21451869663437/50000000000000 : ℝ), (3341174599911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344231999/10000000000 : ℝ)|^8447 ≤ (43731562250703/100000000000000 : ℝ)^6399
        have hw : |(5344231999/10000000000 : ℝ)|=(5344231999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267417939/10000000000 : ℝ)|^8447 ≤ (21451869663437/50000000000000 : ℝ)^6399
        have hw : |(5267417939/10000000000 : ℝ)|=(5267417939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435414543/2000000000 : ℝ)|^8447 ≤ (3341174599911/25000000000000 : ℝ)^6399
        have hw : |(-435414543/2000000000 : ℝ)|=(435414543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s9_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349132343/10000000000 : ℝ)*x 0 + (2112663963/5000000000 : ℝ)*x 1 + (4476451533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349132343/10000000000 : ℝ)^8447 ≤ (33317574700337/100000000000000 : ℝ)^6399 := by
    have hnat : (4349132343 : ℕ)^8447*100000000000000^6399 ≤ 33317574700337^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349132343 10000000000 33317574700337 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112663963/5000000000 : ℝ)^8447 ≤ (16035667732163/50000000000000 : ℝ)^6399 := by
    have hnat : (2112663963 : ℕ)^8447*50000000000000^6399 ≤ 16035667732163^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112663963 5000000000 16035667732163 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476451533/10000000000 : ℝ)^8447 ≤ (34611089821353/100000000000000 : ℝ)^6399 := by
    have hnat : (4476451533 : ℕ)^8447*100000000000000^6399 ≤ 34611089821353^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476451533 10000000000 34611089821353 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349132343/10000000000 : ℝ), (2112663963/5000000000 : ℝ), (4476451533/10000000000 : ℝ)] ![(33317574700337/100000000000000 : ℝ), (16035667732163/50000000000000 : ℝ), (34611089821353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349132343/10000000000 : ℝ)|^8447 ≤ (33317574700337/100000000000000 : ℝ)^6399
        have hw : |(4349132343/10000000000 : ℝ)|=(4349132343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112663963/5000000000 : ℝ)|^8447 ≤ (16035667732163/50000000000000 : ℝ)^6399
        have hw : |(2112663963/5000000000 : ℝ)|=(2112663963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476451533/10000000000 : ℝ)|^8447 ≤ (34611089821353/100000000000000 : ℝ)^6399
        have hw : |(4476451533/10000000000 : ℝ)|=(4476451533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s9_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528614861/2500000000 : ℝ)*x 0 + (5267729307/10000000000 : ℝ)*x 1 + (539061259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528614861/2500000000 : ℝ)^8447 ≤ (12859657723887/100000000000000 : ℝ)^6399 := by
    have hnat : (528614861 : ℕ)^8447*100000000000000^6399 ≤ 12859657723887^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528614861 2500000000 12859657723887 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267729307/10000000000 : ℝ)^8447 ≤ (42907087175677/100000000000000 : ℝ)^6399 := by
    have hnat : (5267729307 : ℕ)^8447*100000000000000^6399 ≤ 42907087175677^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267729307 10000000000 42907087175677 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539061259/1000000000 : ℝ)^8447 ≤ (44233255086687/100000000000000 : ℝ)^6399 := by
    have hnat : (539061259 : ℕ)^8447*100000000000000^6399 ≤ 44233255086687^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539061259 1000000000 44233255086687 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528614861/2500000000 : ℝ), (5267729307/10000000000 : ℝ), (539061259/1000000000 : ℝ)] ![(12859657723887/100000000000000 : ℝ), (42907087175677/100000000000000 : ℝ), (44233255086687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528614861/2500000000 : ℝ)|^8447 ≤ (12859657723887/100000000000000 : ℝ)^6399
        have hw : |(-528614861/2500000000 : ℝ)|=(528614861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267729307/10000000000 : ℝ)|^8447 ≤ (42907087175677/100000000000000 : ℝ)^6399
        have hw : |(5267729307/10000000000 : ℝ)|=(5267729307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539061259/1000000000 : ℝ)|^8447 ≤ (44233255086687/100000000000000 : ℝ)^6399
        have hw : |(539061259/1000000000 : ℝ)|=(539061259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s9_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349141733/10000000000 : ℝ)*x 0 + (4475818441/10000000000 : ℝ)*x 1 + (2112981659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349141733/10000000000 : ℝ)^8447 ≤ (6663533931463/20000000000000 : ℝ)^6399 := by
    have hnat : (4349141733 : ℕ)^8447*20000000000000^6399 ≤ 6663533931463^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349141733 10000000000 6663533931463 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475818441/10000000000 : ℝ)^8447 ≤ (34604628389503/100000000000000 : ℝ)^6399 := by
    have hnat : (4475818441 : ℕ)^8447*100000000000000^6399 ≤ 34604628389503^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475818441 10000000000 34604628389503 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112981659/5000000000 : ℝ)^8447 ≤ (32077701941721/100000000000000 : ℝ)^6399 := by
    have hnat : (2112981659 : ℕ)^8447*100000000000000^6399 ≤ 32077701941721^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112981659 5000000000 32077701941721 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349141733/10000000000 : ℝ), (4475818441/10000000000 : ℝ), (2112981659/5000000000 : ℝ)] ![(6663533931463/20000000000000 : ℝ), (34604628389503/100000000000000 : ℝ), (32077701941721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349141733/10000000000 : ℝ)|^8447 ≤ (6663533931463/20000000000000 : ℝ)^6399
        have hw : |(4349141733/10000000000 : ℝ)|=(4349141733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475818441/10000000000 : ℝ)|^8447 ≤ (34604628389503/100000000000000 : ℝ)^6399
        have hw : |(4475818441/10000000000 : ℝ)|=(4475818441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112981659/5000000000 : ℝ)|^8447 ≤ (32077701941721/100000000000000 : ℝ)^6399
        have hw : |(2112981659/5000000000 : ℝ)|=(2112981659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5747/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11493/100000 : ℝ) ^ (4223/1024 : ℝ) ≤ (13341521123123581/100000000000000000000 : ℝ) := by
    have hpowers : (11493/100000 : ℝ)^4223 ≤ (13341521123123581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11493 : ℕ)^4223*100000000000000000000^1024 ≤ 13341521123123581^1024*100000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11493 100000 13341521123123581 100000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11493/100000 : ℝ)) (X := (13341521123123581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (4223/1024 : ℝ) ≤ (3886328296961849/12500000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^4223 ≤ (3886328296961849/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4223*12500000000000000000^1024 ≤ 3886328296961849^1024*10000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 3886328296961849 12500000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (3886328296961849/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013341521123123581/50000000000000000000 : ℝ) ≤ (10000646949426077/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50013341521123123581/50000000000000000000 : ℝ)^1024 ≤ (10000646949426077/10000000000000000 : ℝ)^4223 := by
      have hnat : (50013341521123123581 : ℕ)^1024*10000000000000000^4223 ≤ 10000646949426077^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013341521123123581 50000000000000000000 10000646949426077 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000646949426077/10000000000000000 : ℝ)) (X := (50013341521123123581/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044432147498818373/100000000000000000000 : ℝ) ≤ (5000538608383229/5000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (100044432147498818373/100000000000000000000 : ℝ)^1024 ≤ (5000538608383229/5000000000000000 : ℝ)^4223 := by
      have hnat : (100044432147498818373 : ℕ)^1024*5000000000000000^4223 ≤ 5000538608383229^4223*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044432147498818373 100000000000000000000 5000538608383229 5000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000538608383229/5000000000000000 : ℝ)) (X := (100044432147498818373/100000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253886328296961849/6250000000000000000 : ℝ) ≤ (10001507484106839/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (6253886328296961849/6250000000000000000 : ℝ)^1024 ≤ (10001507484106839/10000000000000000 : ℝ)^4223 := by
      have hnat : (6253886328296961849 : ℕ)^1024*10000000000000000^4223 ≤ 10001507484106839^4223*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253886328296961849 6250000000000000000 10001507484106839 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001507484106839/10000000000000000 : ℝ)) (X := (6253886328296961849/6250000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13341521123123581/100000000000000000000 : ℝ) ≤ ((26161802941562045843/26170000000000000000 : ℝ)+2*(430267340381/261700000000000 : ℝ)*(11493/100000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (26161802941562045843/26170000000000000000 : ℝ)+2*(430267340381/261700000000000 : ℝ)*(11493/100000 : ℝ)=(10000646949426077/10000000000000000 : ℝ) by norm_num, show 1+2*(13341521123123581/100000000000000000000 : ℝ)=(50013341521123123581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3886328296961849/12500000000000000000 : ℝ)+(13341521123123581/100000000000000000000 : ℝ) ≤ ((26161802941562045843/26170000000000000000 : ℝ)+(430267340381/261700000000000 : ℝ)*((1411/10000 : ℝ)+(11493/100000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (26161802941562045843/26170000000000000000 : ℝ)+(430267340381/261700000000000 : ℝ)*((1411/10000 : ℝ)+(11493/100000 : ℝ))=(5000538608383229/5000000000000000 : ℝ) by norm_num, show 1+(3886328296961849/12500000000000000000 : ℝ)+(13341521123123581/100000000000000000000 : ℝ)=(100044432147498818373/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3886328296961849/12500000000000000000 : ℝ) ≤ ((26161802941562045843/26170000000000000000 : ℝ)+2*(430267340381/261700000000000 : ℝ)*(1411/10000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (26161802941562045843/26170000000000000000 : ℝ)+2*(430267340381/261700000000000 : ℝ)*(1411/10000 : ℝ)=(10001507484106839/10000000000000000 : ℝ) by norm_num, show 1+2*(3886328296961849/12500000000000000000 : ℝ)=(6253886328296961849/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26161802941562045843/26170000000000000000 : ℝ)*(X 1 0+X 2 0)+(430267340381/261700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (26161802941562045843/26170000000000000000 : ℝ)) (alpha := (430267340381/261700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26161802941562045843/26170000000000000000 : ℝ)*(X 0 1+X 2 1)+(430267340381/261700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (26161802941562045843/26170000000000000000 : ℝ)) (alpha := (430267340381/261700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26161802941562045843/26170000000000000000 : ℝ)*(X 0 2+X 1 2)+(430267340381/261700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11493/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (26161802941562045843/26170000000000000000 : ℝ)) (alpha := (430267340381/261700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2114454819/10000000000 : ℝ)*X 0 0+(5390925087/10000000000 : ℝ)*X 0 1+(2633708971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668029/1250000 : ℝ)*X 1 0+(-217707271/1000000000 : ℝ)*X 1 1+(5267417943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344231999/10000000000 : ℝ)*X 2 0+(5267417939/10000000000 : ℝ)*X 2 1+(-435414543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349132343/10000000000 : ℝ)*X 0 0+(2112663963/5000000000 : ℝ)*X 0 1+(4476451533/10000000000 : ℝ)*X 0 2+(4349132343/10000000000 : ℝ)*X 1 0+(2112663963/5000000000 : ℝ)*X 1 1+(4476451533/10000000000 : ℝ)*X 1 2+(4349132343/10000000000 : ℝ)*X 2 0+(2112663963/5000000000 : ℝ)*X 2 1+(4476451533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528614861/2500000000 : ℝ)*X 0 0+(5267729307/10000000000 : ℝ)*X 0 1+(539061259/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4349141733/10000000000 : ℝ)*X 0 0+(4475818441/10000000000 : ℝ)*X 0 1+(2112981659/5000000000 : ℝ)*X 0 2+(4349141733/10000000000 : ℝ)*X 1 0+(4475818441/10000000000 : ℝ)*X 1 1+(2112981659/5000000000 : ℝ)*X 1 2+(4349141733/10000000000 : ℝ)*X 2 0+(4475818441/10000000000 : ℝ)*X 2 1+(2112981659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255128880970129874265086313/130850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77085703/20000000000000 : ℝ)*(base19) + (347742379/100000000000000 : ℝ)*(base23) + (9665337/50000000000000 : ℝ)*(lower2) + (28742101/50000000000000 : ℝ)*(upper3) + (5317263/25000000000000 : ℝ)*(upper5) + (603941629175903/10000000000000 : ℝ)*(major0) + (603941629175903/10000000000000 : ℝ)*(major1) + (603941629175903/10000000000000 : ℝ)*(major2) + (1012088617991353/12500000000000 : ℝ)*(sp0) + (4048359382260061/50000000000000 : ℝ)*(sp1) + (8096718802206259/100000000000000 : ℝ)*(sp2) + (1991053777755423/50000000000000 : ℝ)*(sp3) + (5103008907/50000000000000 : ℝ)*(sp4) + (2906532929/50000000000000 : ℝ)*(sp5) + (62220521384011/1562500000000 : ℝ)*(f.failure) + (4048359574974319/50000000000000 : ℝ)*(f.sum) + (4733349946573/1308500000000000000000000000 : ℝ)*base65 + (2706695547189221229/261700000000000000000000000000000 : ℝ)*base67 + (3065141622310221229/261700000000000000000000000000000 : ℝ)*base69 + (724615074975178771/261700000000000000000000000000000 : ℝ)*base72 + (1676876735267/654250000000000000000000000 : ℝ)*base73 + (4072627326847621229/261700000000000000000000000000000 : ℝ)*base75 + (857971569794878771/261700000000000000000000000000000 : ℝ)*base78 + (254926747143721229/261700000000000000000000000000000 : ℝ)*base79 + (14562698268077/2617000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (119091/31250000000000000000 : ℝ)*base90 + (119091/31250000000000000000 : ℝ)*base92 + (119091/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1254_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1254_box_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-995568063/5000000000 : ℝ)*x 0 + (5374658303/10000000000 : ℝ)*x 1 + (5374658263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995568063/5000000000 : ℝ)^8447 ≤ (1187895415473/10000000000000 : ℝ)^6399 := by
    have hnat : (995568063 : ℕ)^8447*10000000000000^6399 ≤ 1187895415473^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995568063 5000000000 1187895415473 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374658303/10000000000 : ℝ)^8447 ≤ (11015130783087/25000000000000 : ℝ)^6399 := by
    have hnat : (5374658303 : ℕ)^8447*25000000000000^6399 ≤ 11015130783087^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374658303 10000000000 11015130783087 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374658263/10000000000 : ℝ)^8447 ≤ (22030261349743/50000000000000 : ℝ)^6399 := by
    have hnat : (5374658263 : ℕ)^8447*50000000000000^6399 ≤ 22030261349743^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374658263 10000000000 22030261349743 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-995568063/5000000000 : ℝ), (5374658303/10000000000 : ℝ), (5374658263/10000000000 : ℝ)] ![(1187895415473/10000000000000 : ℝ), (11015130783087/25000000000000 : ℝ), (22030261349743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-995568063/5000000000 : ℝ)|^8447 ≤ (1187895415473/10000000000000 : ℝ)^6399
        have hw : |(-995568063/5000000000 : ℝ)|=(995568063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374658303/10000000000 : ℝ)|^8447 ≤ (11015130783087/25000000000000 : ℝ)^6399
        have hw : |(5374658303/10000000000 : ℝ)|=(5374658303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374658263/10000000000 : ℝ)|^8447 ≤ (22030261349743/50000000000000 : ℝ)^6399
        have hw : |(5374658263/10000000000 : ℝ)|=(5374658263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1324219789/2500000000 : ℝ)*x 0 + (-524219223/2500000000 : ℝ)*x 1 + (5374658259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324219789/2500000000 : ℝ)^8447 ≤ (43220788392917/100000000000000 : ℝ)^6399 := by
    have hnat : (1324219789 : ℕ)^8447*100000000000000^6399 ≤ 43220788392917^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324219789 2500000000 43220788392917 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524219223/2500000000 : ℝ)^8447 ≤ (508747557481/4000000000000 : ℝ)^6399 := by
    have hnat : (524219223 : ℕ)^8447*4000000000000^6399 ≤ 508747557481^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524219223 2500000000 508747557481 4000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374658259/10000000000 : ℝ)^8447 ≤ (220302613281/500000000000 : ℝ)^6399 := by
    have hnat : (5374658259 : ℕ)^8447*500000000000^6399 ≤ 220302613281^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374658259 10000000000 220302613281 500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324219789/2500000000 : ℝ), (-524219223/2500000000 : ℝ), (5374658259/10000000000 : ℝ)] ![(43220788392917/100000000000000 : ℝ), (508747557481/4000000000000 : ℝ), (220302613281/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324219789/2500000000 : ℝ)|^8447 ≤ (43220788392917/100000000000000 : ℝ)^6399
        have hw : |(1324219789/2500000000 : ℝ)|=(1324219789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524219223/2500000000 : ℝ)|^8447 ≤ (508747557481/4000000000000 : ℝ)^6399
        have hw : |(-524219223/2500000000 : ℝ)|=(524219223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374658259/10000000000 : ℝ)|^8447 ≤ (220302613281/500000000000 : ℝ)^6399
        have hw : |(5374658259/10000000000 : ℝ)|=(5374658259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (331054943/625000000 : ℝ)*x 0 + (1343664587/2500000000 : ℝ)*x 1 + (-32763701/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331054943/625000000 : ℝ)^8447 ≤ (43220787660477/100000000000000 : ℝ)^6399 := by
    have hnat : (331054943 : ℕ)^8447*100000000000000^6399 ≤ 43220787660477^6399*625000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331054943 625000000 43220787660477 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343664587/2500000000 : ℝ)^8447 ≤ (44060523619317/100000000000000 : ℝ)^6399 := by
    have hnat : (1343664587 : ℕ)^8447*100000000000000^6399 ≤ 44060523619317^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343664587 2500000000 44060523619317 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32763701/156250000 : ℝ)^8447 ≤ (2543737742567/20000000000000 : ℝ)^6399 := by
    have hnat : (32763701 : ℕ)^8447*20000000000000^6399 ≤ 2543737742567^6399*156250000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32763701 156250000 2543737742567 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331054943/625000000 : ℝ), (1343664587/2500000000 : ℝ), (-32763701/156250000 : ℝ)] ![(43220787660477/100000000000000 : ℝ), (44060523619317/100000000000000 : ℝ), (2543737742567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331054943/625000000 : ℝ)|^8447 ≤ (43220787660477/100000000000000 : ℝ)^6399
        have hw : |(331054943/625000000 : ℝ)|=(331054943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343664587/2500000000 : ℝ)|^8447 ≤ (44060523619317/100000000000000 : ℝ)^6399
        have hw : |(1343664587/2500000000 : ℝ)|=(1343664587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32763701/156250000 : ℝ)|^8447 ≤ (2543737742567/20000000000000 : ℝ)^6399
        have hw : |(-32763701/156250000 : ℝ)|=(32763701/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1113884311/2500000000 : ℝ)*x 0 + (268622731/625000000 : ℝ)*x 1 + (4297963561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113884311/2500000000 : ℝ)^8447 ≤ (3439779038337/10000000000000 : ℝ)^6399 := by
    have hnat : (1113884311 : ℕ)^8447*10000000000000^6399 ≤ 3439779038337^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113884311 2500000000 3439779038337 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268622731/625000000 : ℝ)^8447 ≤ (16400552738427/50000000000000 : ℝ)^6399 := by
    have hnat : (268622731 : ℕ)^8447*50000000000000^6399 ≤ 16400552738427^6399*625000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268622731 625000000 16400552738427 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4297963561/10000000000 : ℝ)^8447 ≤ (32801104116819/100000000000000 : ℝ)^6399 := by
    have hnat : (4297963561 : ℕ)^8447*100000000000000^6399 ≤ 32801104116819^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297963561 10000000000 32801104116819 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1113884311/2500000000 : ℝ), (268622731/625000000 : ℝ), (4297963561/10000000000 : ℝ)] ![(3439779038337/10000000000000 : ℝ), (16400552738427/50000000000000 : ℝ), (32801104116819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1113884311/2500000000 : ℝ)|^8447 ≤ (3439779038337/10000000000000 : ℝ)^6399
        have hw : |(1113884311/2500000000 : ℝ)|=(1113884311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268622731/625000000 : ℝ)|^8447 ≤ (16400552738427/50000000000000 : ℝ)^6399
        have hw : |(268622731/625000000 : ℝ)|=(268622731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4297963561/10000000000 : ℝ)|^8447 ≤ (32801104116819/100000000000000 : ℝ)^6399
        have hw : |(4297963561/10000000000 : ℝ)|=(4297963561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2239147429/10000000000 : ℝ)*x 0 + (5282409067/10000000000 : ℝ)*x 1 + (1056481823/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239147429/10000000000 : ℝ)^8447 ≤ (13870005993487/100000000000000 : ℝ)^6399 := by
    have hnat : (2239147429 : ℕ)^8447*100000000000000^6399 ≤ 13870005993487^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239147429 10000000000 13870005993487 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282409067/10000000000 : ℝ)^8447 ≤ (4306499673783/10000000000000 : ℝ)^6399 := by
    have hnat : (5282409067 : ℕ)^8447*10000000000000^6399 ≤ 4306499673783^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282409067 10000000000 4306499673783 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056481823/2000000000 : ℝ)^8447 ≤ (21532498627197/50000000000000 : ℝ)^6399 := by
    have hnat : (1056481823 : ℕ)^8447*50000000000000^6399 ≤ 21532498627197^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056481823 2000000000 21532498627197 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2239147429/10000000000 : ℝ), (5282409067/10000000000 : ℝ), (1056481823/2000000000 : ℝ)] ![(13870005993487/100000000000000 : ℝ), (4306499673783/10000000000000 : ℝ), (21532498627197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2239147429/10000000000 : ℝ)|^8447 ≤ (13870005993487/100000000000000 : ℝ)^6399
        have hw : |(-2239147429/10000000000 : ℝ)|=(2239147429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282409067/10000000000 : ℝ)|^8447 ≤ (4306499673783/10000000000000 : ℝ)^6399
        have hw : |(5282409067/10000000000 : ℝ)|=(5282409067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056481823/2000000000 : ℝ)|^8447 ≤ (21532498627197/50000000000000 : ℝ)^6399
        have hw : |(1056481823/2000000000 : ℝ)|=(1056481823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361891331/10000000000 : ℝ)*x 0 + (-426696187/2000000000 : ℝ)*x 1 + (1056481807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361891331/10000000000 : ℝ)^8447 ≤ (43922417346247/100000000000000 : ℝ)^6399 := by
    have hnat : (5361891331 : ℕ)^8447*100000000000000^6399 ≤ 43922417346247^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361891331 10000000000 43922417346247 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426696187/2000000000 : ℝ)^8447 ≤ (13012586238371/100000000000000 : ℝ)^6399 := by
    have hnat : (426696187 : ℕ)^8447*100000000000000^6399 ≤ 13012586238371^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426696187 2000000000 13012586238371 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056481807/2000000000 : ℝ)^8447 ≤ (8612999278691/20000000000000 : ℝ)^6399 := by
    have hnat : (1056481807 : ℕ)^8447*20000000000000^6399 ≤ 8612999278691^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056481807 2000000000 8612999278691 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361891331/10000000000 : ℝ), (-426696187/2000000000 : ℝ), (1056481807/2000000000 : ℝ)] ![(43922417346247/100000000000000 : ℝ), (13012586238371/100000000000000 : ℝ), (8612999278691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361891331/10000000000 : ℝ)|^8447 ≤ (43922417346247/100000000000000 : ℝ)^6399
        have hw : |(5361891331/10000000000 : ℝ)|=(5361891331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426696187/2000000000 : ℝ)|^8447 ≤ (13012586238371/100000000000000 : ℝ)^6399
        have hw : |(-426696187/2000000000 : ℝ)|=(426696187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056481807/2000000000 : ℝ)|^8447 ≤ (8612999278691/20000000000000 : ℝ)^6399
        have hw : |(1056481807/2000000000 : ℝ)|=(1056481807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361891327/10000000000 : ℝ)*x 0 + (5282409059/10000000000 : ℝ)*x 1 + (-213348091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361891327/10000000000 : ℝ)^8447 ≤ (21961208651497/50000000000000 : ℝ)^6399 := by
    have hnat : (5361891327 : ℕ)^8447*50000000000000^6399 ≤ 21961208651497^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361891327 10000000000 21961208651497 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282409059/10000000000 : ℝ)^8447 ≤ (5383124581467/12500000000000 : ℝ)^6399 := by
    have hnat : (5282409059 : ℕ)^8447*12500000000000^6399 ≤ 5383124581467^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282409059 10000000000 5383124581467 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213348091/1000000000 : ℝ)^8447 ≤ (13012586037089/100000000000000 : ℝ)^6399 := by
    have hnat : (213348091 : ℕ)^8447*100000000000000^6399 ≤ 13012586037089^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213348091 1000000000 13012586037089 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361891327/10000000000 : ℝ), (5282409059/10000000000 : ℝ), (-213348091/1000000000 : ℝ)] ![(21961208651497/50000000000000 : ℝ), (5383124581467/12500000000000 : ℝ), (13012586037089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361891327/10000000000 : ℝ)|^8447 ≤ (21961208651497/50000000000000 : ℝ)^6399
        have hw : |(5361891327/10000000000 : ℝ)|=(5361891327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282409059/10000000000 : ℝ)|^8447 ≤ (5383124581467/12500000000000 : ℝ)^6399
        have hw : |(5282409059/10000000000 : ℝ)|=(5282409059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213348091/1000000000 : ℝ)|^8447 ≤ (13012586037089/100000000000000 : ℝ)^6399
        have hw : |(-213348091/1000000000 : ℝ)|=(213348091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4242320101/10000000000 : ℝ)*x 0 + (4404552191/10000000000 : ℝ)*x 1 + (4404552187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242320101/10000000000 : ℝ)^8447 ≤ (32241698403089/100000000000000 : ℝ)^6399 := by
    have hnat : (4242320101 : ℕ)^8447*100000000000000^6399 ≤ 32241698403089^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242320101 10000000000 32241698403089 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4404552191/10000000000 : ℝ)^8447 ≤ (33879150811163/100000000000000 : ℝ)^6399 := by
    have hnat : (4404552191 : ℕ)^8447*100000000000000^6399 ≤ 33879150811163^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404552191 10000000000 33879150811163 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4404552187/10000000000 : ℝ)^8447 ≤ (33879150770549/100000000000000 : ℝ)^6399 := by
    have hnat : (4404552187 : ℕ)^8447*100000000000000^6399 ≤ 33879150770549^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404552187 10000000000 33879150770549 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242320101/10000000000 : ℝ), (4404552191/10000000000 : ℝ), (4404552187/10000000000 : ℝ)] ![(32241698403089/100000000000000 : ℝ), (33879150811163/100000000000000 : ℝ), (33879150770549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242320101/10000000000 : ℝ)|^8447 ≤ (32241698403089/100000000000000 : ℝ)^6399
        have hw : |(4242320101/10000000000 : ℝ)|=(4242320101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4404552191/10000000000 : ℝ)|^8447 ≤ (33879150811163/100000000000000 : ℝ)^6399
        have hw : |(4404552191/10000000000 : ℝ)|=(4404552191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4404552187/10000000000 : ℝ)|^8447 ≤ (33879150770549/100000000000000 : ℝ)^6399
        have hw : |(4404552187/10000000000 : ℝ)|=(4404552187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_8 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-546791187/2500000000 : ℝ)*x 0 + (2609731573/5000000000 : ℝ)*x 1 + (1076854171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546791187/2500000000 : ℝ)^8447 ≤ (13446540540491/100000000000000 : ℝ)^6399 := by
    have hnat : (546791187 : ℕ)^8447*100000000000000^6399 ≤ 13446540540491^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546791187 2500000000 13446540540491 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609731573/5000000000 : ℝ)^8447 ≤ (211944419557/500000000000 : ℝ)^6399 := by
    have hnat : (2609731573 : ℕ)^8447*500000000000^6399 ≤ 211944419557^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609731573 5000000000 211944419557 500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076854171/2000000000 : ℝ)^8447 ≤ (44164575533159/100000000000000 : ℝ)^6399 := by
    have hnat : (1076854171 : ℕ)^8447*100000000000000^6399 ≤ 44164575533159^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076854171 2000000000 44164575533159 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546791187/2500000000 : ℝ), (2609731573/5000000000 : ℝ), (1076854171/2000000000 : ℝ)] ![(13446540540491/100000000000000 : ℝ), (211944419557/500000000000 : ℝ), (44164575533159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546791187/2500000000 : ℝ)|^8447 ≤ (13446540540491/100000000000000 : ℝ)^6399
        have hw : |(-546791187/2500000000 : ℝ)|=(546791187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609731573/5000000000 : ℝ)|^8447 ≤ (211944419557/500000000000 : ℝ)^6399
        have hw : |(2609731573/5000000000 : ℝ)|=(2609731573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076854171/2000000000 : ℝ)|^8447 ≤ (44164575533159/100000000000000 : ℝ)^6399
        have hw : |(1076854171/2000000000 : ℝ)|=(1076854171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_9 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322525517/2500000000 : ℝ)*x 0 + (-523248919/2500000000 : ℝ)*x 1 + (1346067629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322525517/2500000000 : ℝ)^8447 ≤ (43147806155303/100000000000000 : ℝ)^6399 := by
    have hnat : (1322525517 : ℕ)^8447*100000000000000^6399 ≤ 43147806155303^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322525517 2500000000 43147806155303 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523248919/2500000000 : ℝ)^8447 ≤ (3171905491743/25000000000000 : ℝ)^6399 := by
    have hnat : (523248919 : ℕ)^8447*25000000000000^6399 ≤ 3171905491743^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523248919 2500000000 3171905491743 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346067629/2500000000 : ℝ)^8447 ≤ (44164571862557/100000000000000 : ℝ)^6399 := by
    have hnat : (1346067629 : ℕ)^8447*100000000000000^6399 ≤ 44164571862557^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346067629 2500000000 44164571862557 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322525517/2500000000 : ℝ), (-523248919/2500000000 : ℝ), (1346067629/2500000000 : ℝ)] ![(43147806155303/100000000000000 : ℝ), (3171905491743/25000000000000 : ℝ), (44164571862557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322525517/2500000000 : ℝ)|^8447 ≤ (43147806155303/100000000000000 : ℝ)^6399
        have hw : |(1322525517/2500000000 : ℝ)|=(1322525517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523248919/2500000000 : ℝ)|^8447 ≤ (3171905491743/25000000000000 : ℝ)^6399
        have hw : |(-523248919/2500000000 : ℝ)|=(523248919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346067629/2500000000 : ℝ)|^8447 ≤ (44164571862557/100000000000000 : ℝ)^6399
        have hw : |(1346067629/2500000000 : ℝ)|=(1346067629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_10 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2645050893/5000000000 : ℝ)*x 0 + (1076854229/2000000000 : ℝ)*x 1 + (-418599041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645050893/5000000000 : ℝ)^8447 ≤ (43147803119077/100000000000000 : ℝ)^6399 := by
    have hnat : (2645050893 : ℕ)^8447*100000000000000^6399 ≤ 43147803119077^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645050893 5000000000 43147803119077 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076854229/2000000000 : ℝ)^8447 ≤ (22082289336601/50000000000000 : ℝ)^6399 := by
    have hnat : (1076854229 : ℕ)^8447*50000000000000^6399 ≤ 22082289336601^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076854229 2000000000 22082289336601 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418599041/2000000000 : ℝ)^8447 ≤ (6343809098999/50000000000000 : ℝ)^6399 := by
    have hnat : (418599041 : ℕ)^8447*50000000000000^6399 ≤ 6343809098999^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418599041 2000000000 6343809098999 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645050893/5000000000 : ℝ), (1076854229/2000000000 : ℝ), (-418599041/2000000000 : ℝ)] ![(43147803119077/100000000000000 : ℝ), (22082289336601/50000000000000 : ℝ), (6343809098999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645050893/5000000000 : ℝ)|^8447 ≤ (43147803119077/100000000000000 : ℝ)^6399
        have hw : |(2645050893/5000000000 : ℝ)|=(2645050893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076854229/2000000000 : ℝ)|^8447 ≤ (22082289336601/50000000000000 : ℝ)^6399
        have hw : |(1076854229/2000000000 : ℝ)|=(1076854229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418599041/2000000000 : ℝ)|^8447 ≤ (6343809098999/50000000000000 : ℝ)^6399
        have hw : |(-418599041/2000000000 : ℝ)|=(418599041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_11 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (179099303/400000000 : ℝ)*x 0 + (2143425221/5000000000 : ℝ)*x 1 + (4286850447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179099303/400000000 : ℝ)^8447 ≤ (34621613416563/100000000000000 : ℝ)^6399 := by
    have hnat : (179099303 : ℕ)^8447*100000000000000^6399 ≤ 34621613416563^6399*400000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179099303 400000000 34621613416563 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143425221/5000000000 : ℝ)^8447 ≤ (32689193254831/100000000000000 : ℝ)^6399 := by
    have hnat : (2143425221 : ℕ)^8447*100000000000000^6399 ≤ 32689193254831^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143425221 5000000000 32689193254831 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4286850447/10000000000 : ℝ)^8447 ≤ (32689193305161/100000000000000 : ℝ)^6399 := by
    have hnat : (4286850447 : ℕ)^8447*100000000000000^6399 ≤ 32689193305161^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286850447 10000000000 32689193305161 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179099303/400000000 : ℝ), (2143425221/5000000000 : ℝ), (4286850447/10000000000 : ℝ)] ![(34621613416563/100000000000000 : ℝ), (32689193254831/100000000000000 : ℝ), (32689193305161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179099303/400000000 : ℝ)|^8447 ≤ (34621613416563/100000000000000 : ℝ)^6399
        have hw : |(179099303/400000000 : ℝ)|=(179099303/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2143425221/5000000000 : ℝ)|^8447 ≤ (32689193254831/100000000000000 : ℝ)^6399
        have hw : |(2143425221/5000000000 : ℝ)|=(2143425221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4286850447/10000000000 : ℝ)|^8447 ≤ (32689193305161/100000000000000 : ℝ)^6399
        have hw : |(4286850447/10000000000 : ℝ)|=(4286850447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_12 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021685879/5000000000 : ℝ)*x 0 + (5436403593/10000000000 : ℝ)*x 1 + (82411343/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021685879/5000000000 : ℝ)^8447 ≤ (12292042757607/100000000000000 : ℝ)^6399 := by
    have hnat : (1021685879 : ℕ)^8447*100000000000000^6399 ≤ 12292042757607^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021685879 5000000000 12292042757607 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436403593/10000000000 : ℝ)^8447 ≤ (22364963809879/50000000000000 : ℝ)^6399 := by
    have hnat : (5436403593 : ℕ)^8447*50000000000000^6399 ≤ 22364963809879^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436403593 10000000000 22364963809879 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82411343/156250000 : ℝ)^8447 ≤ (5372253701053/12500000000000 : ℝ)^6399 := by
    have hnat : (82411343 : ℕ)^8447*12500000000000^6399 ≤ 5372253701053^6399*156250000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82411343 156250000 5372253701053 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021685879/5000000000 : ℝ), (5436403593/10000000000 : ℝ), (82411343/156250000 : ℝ)] ![(12292042757607/100000000000000 : ℝ), (22364963809879/50000000000000 : ℝ), (5372253701053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021685879/5000000000 : ℝ)|^8447 ≤ (12292042757607/100000000000000 : ℝ)^6399
        have hw : |(-1021685879/5000000000 : ℝ)|=(1021685879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436403593/10000000000 : ℝ)|^8447 ≤ (22364963809879/50000000000000 : ℝ)^6399
        have hw : |(5436403593/10000000000 : ℝ)|=(5436403593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82411343/156250000 : ℝ)|^8447 ≤ (5372253701053/12500000000000 : ℝ)^6399
        have hw : |(82411343/156250000 : ℝ)|=(82411343/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_13 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335474151/625000000 : ℝ)*x 0 + (-534158081/2500000000 : ℝ)*x 1 + (1318581369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335474151/625000000 : ℝ)^8447 ≤ (43984010524323/100000000000000 : ℝ)^6399 := by
    have hnat : (335474151 : ℕ)^8447*100000000000000^6399 ≤ 43984010524323^6399*625000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335474151 625000000 43984010524323 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534158081/2500000000 : ℝ)^8447 ≤ (6518982483531/50000000000000 : ℝ)^6399 := by
    have hnat : (534158081 : ℕ)^8447*50000000000000^6399 ≤ 6518982483531^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534158081 2500000000 6518982483531 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318581369/2500000000 : ℝ)^8447 ≤ (21489012244171/50000000000000 : ℝ)^6399 := by
    have hnat : (1318581369 : ℕ)^8447*50000000000000^6399 ≤ 21489012244171^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318581369 2500000000 21489012244171 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335474151/625000000 : ℝ), (-534158081/2500000000 : ℝ), (1318581369/2500000000 : ℝ)] ![(43984010524323/100000000000000 : ℝ), (6518982483531/50000000000000 : ℝ), (21489012244171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335474151/625000000 : ℝ)|^8447 ≤ (43984010524323/100000000000000 : ℝ)^6399
        have hw : |(335474151/625000000 : ℝ)|=(335474151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534158081/2500000000 : ℝ)|^8447 ≤ (6518982483531/50000000000000 : ℝ)^6399
        have hw : |(-534158081/2500000000 : ℝ)|=(534158081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318581369/2500000000 : ℝ)|^8447 ≤ (21489012244171/50000000000000 : ℝ)^6399
        have hw : |(1318581369/2500000000 : ℝ)|=(1318581369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_14 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367586161/10000000000 : ℝ)*x 0 + (5274325573/10000000000 : ℝ)*x 1 + (-1068316269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367586161/10000000000 : ℝ)^8447 ≤ (5498000970749/12500000000000 : ℝ)^6399 := by
    have hnat : (5367586161 : ℕ)^8447*12500000000000^6399 ≤ 5498000970749^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367586161 10000000000 5498000970749 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274325573/10000000000 : ℝ)^8447 ≤ (1074450638293/2500000000000 : ℝ)^6399 := by
    have hnat : (5274325573 : ℕ)^8447*2500000000000^6399 ≤ 1074450638293^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274325573 10000000000 1074450638293 2500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068316269/5000000000 : ℝ)^8447 ≤ (13037966690851/100000000000000 : ℝ)^6399 := by
    have hnat : (1068316269 : ℕ)^8447*100000000000000^6399 ≤ 13037966690851^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068316269 5000000000 13037966690851 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367586161/10000000000 : ℝ), (5274325573/10000000000 : ℝ), (-1068316269/5000000000 : ℝ)] ![(5498000970749/12500000000000 : ℝ), (1074450638293/2500000000000 : ℝ), (13037966690851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367586161/10000000000 : ℝ)|^8447 ≤ (5498000970749/12500000000000 : ℝ)^6399
        have hw : |(5367586161/10000000000 : ℝ)|=(5367586161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274325573/10000000000 : ℝ)|^8447 ≤ (1074450638293/2500000000000 : ℝ)^6399
        have hw : |(5274325573/10000000000 : ℝ)|=(5274325573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1068316269/5000000000 : ℝ)|^8447 ≤ (13037966690851/100000000000000 : ℝ)^6399
        have hw : |(-1068316269/5000000000 : ℝ)|=(1068316269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_box_15 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (844681021/2000000000 : ℝ)*x 0 + (4413886747/10000000000 : ℝ)*x 1 + (2206943561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844681021/2000000000 : ℝ)^8447 ≤ (6410414223981/20000000000000 : ℝ)^6399 := by
    have hnat : (844681021 : ℕ)^8447*20000000000000^6399 ≤ 6410414223981^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844681021 2000000000 6410414223981 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413886747/10000000000 : ℝ)^8447 ≤ (4246745315607/12500000000000 : ℝ)^6399 := by
    have hnat : (4413886747 : ℕ)^8447*12500000000000^6399 ≤ 4246745315607^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413886747 10000000000 4246745315607 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206943561/5000000000 : ℝ)^8447 ≤ (16986983167523/50000000000000 : ℝ)^6399 := by
    have hnat : (2206943561 : ℕ)^8447*50000000000000^6399 ≤ 16986983167523^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206943561 5000000000 16986983167523 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844681021/2000000000 : ℝ), (4413886747/10000000000 : ℝ), (2206943561/5000000000 : ℝ)] ![(6410414223981/20000000000000 : ℝ), (4246745315607/12500000000000 : ℝ), (16986983167523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844681021/2000000000 : ℝ)|^8447 ≤ (6410414223981/20000000000000 : ℝ)^6399
        have hw : |(844681021/2000000000 : ℝ)|=(844681021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413886747/10000000000 : ℝ)|^8447 ≤ (4246745315607/12500000000000 : ℝ)^6399
        have hw : |(4413886747/10000000000 : ℝ)|=(4413886747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2206943561/5000000000 : ℝ)|^8447 ≤ (16986983167523/50000000000000 : ℝ)^6399
        have hw : |(2206943561/5000000000 : ℝ)|=(2206943561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62249/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59387/100000 : ℝ) ∧ (5009/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20843/25000 : ℝ) := by
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
  have lower0 : (5747/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5747/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5747/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5747/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5747/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5747/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5747/50000 : ℝ) ^ (4223/1024 : ℝ) ≤ (1334630910051197/10000000000000000000 : ℝ) := by
    have hpowers : (5747/50000 : ℝ)^4223 ≤ (1334630910051197/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5747 : ℕ)^4223*10000000000000000000^1024 ≤ 1334630910051197^1024*50000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5747 50000 1334630910051197 10000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5747/50000 : ℝ)) (X := (1334630910051197/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (4223/1024 : ℝ) ≤ (3886328296961849/12500000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^4223 ≤ (3886328296961849/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4223*12500000000000000000^1024 ≤ 3886328296961849^1024*10000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 3886328296961849 12500000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (3886328296961849/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001334630910051197/5000000000000000000 : ℝ) ≤ (400025887263139/400000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (5001334630910051197/5000000000000000000 : ℝ)^1024 ≤ (400025887263139/400000000000000 : ℝ)^4223 := by
      have hnat : (5001334630910051197 : ℕ)^1024*400000000000000^4223 ≤ 400025887263139^4223*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001334630910051197 5000000000000000000 400025887263139 400000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025887263139/400000000000000 : ℝ)) (X := (5001334630910051197/5000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022218467738103381/50000000000000000000 : ℝ) ≤ (10001077332827059/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50022218467738103381/50000000000000000000 : ℝ)^1024 ≤ (10001077332827059/10000000000000000 : ℝ)^4223 := by
      have hnat : (50022218467738103381 : ℕ)^1024*10000000000000000^4223 ≤ 10001077332827059^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022218467738103381 50000000000000000000 10001077332827059 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001077332827059/10000000000000000 : ℝ)) (X := (50022218467738103381/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253886328296961849/6250000000000000000 : ℝ) ≤ (10001507484075643/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (6253886328296961849/6250000000000000000 : ℝ)^1024 ≤ (10001507484075643/10000000000000000 : ℝ)^4223 := by
      have hnat : (6253886328296961849 : ℕ)^1024*10000000000000000^4223 ≤ 10001507484075643^4223*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253886328296961849 6250000000000000000 10001507484075643 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001507484075643/10000000000000000 : ℝ)) (X := (6253886328296961849/6250000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1334630910051197/10000000000000000000 : ℝ) ≤ ((1089658529587785067/1090000000000000000 : ℝ)+2*(17922968691/10900000000000 : ℝ)*(5747/50000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1089658529587785067/1090000000000000000 : ℝ)+2*(17922968691/10900000000000 : ℝ)*(5747/50000 : ℝ)=(400025887263139/400000000000000 : ℝ) by norm_num, show 1+2*(1334630910051197/10000000000000000000 : ℝ)=(5001334630910051197/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3886328296961849/12500000000000000000 : ℝ)+(1334630910051197/10000000000000000000 : ℝ) ≤ ((1089658529587785067/1090000000000000000 : ℝ)+(17922968691/10900000000000 : ℝ)*((1411/10000 : ℝ)+(5747/50000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (1089658529587785067/1090000000000000000 : ℝ)+(17922968691/10900000000000 : ℝ)*((1411/10000 : ℝ)+(5747/50000 : ℝ))=(10001077332827059/10000000000000000 : ℝ) by norm_num, show 1+(3886328296961849/12500000000000000000 : ℝ)+(1334630910051197/10000000000000000000 : ℝ)=(50022218467738103381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3886328296961849/12500000000000000000 : ℝ) ≤ ((1089658529587785067/1090000000000000000 : ℝ)+2*(17922968691/10900000000000 : ℝ)*(1411/10000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1089658529587785067/1090000000000000000 : ℝ)+2*(17922968691/10900000000000 : ℝ)*(1411/10000 : ℝ)=(10001507484075643/10000000000000000 : ℝ) by norm_num, show 1+2*(3886328296961849/12500000000000000000 : ℝ)=(6253886328296961849/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1089658529587785067/1090000000000000000 : ℝ)*(X 1 0+X 2 0)+(17922968691/10900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (1089658529587785067/1090000000000000000 : ℝ)) (alpha := (17922968691/10900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1089658529587785067/1090000000000000000 : ℝ)*(X 0 1+X 2 1)+(17922968691/10900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (1089658529587785067/1090000000000000000 : ℝ)) (alpha := (17922968691/10900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1089658529587785067/1090000000000000000 : ℝ)*(X 0 2+X 1 2)+(17922968691/10900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (1089658529587785067/1090000000000000000 : ℝ)) (alpha := (17922968691/10900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-995568063/5000000000 : ℝ)*X 0 0+(5374658303/10000000000 : ℝ)*X 0 1+(5374658263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1324219789/2500000000 : ℝ)*X 1 0+(-524219223/2500000000 : ℝ)*X 1 1+(5374658259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((331054943/625000000 : ℝ)*X 2 0+(1343664587/2500000000 : ℝ)*X 2 1+(-32763701/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1113884311/2500000000 : ℝ)*X 0 0+(268622731/625000000 : ℝ)*X 0 1+(4297963561/10000000000 : ℝ)*X 0 2+(1113884311/2500000000 : ℝ)*X 1 0+(268622731/625000000 : ℝ)*X 1 1+(4297963561/10000000000 : ℝ)*X 1 2+(1113884311/2500000000 : ℝ)*X 2 0+(268622731/625000000 : ℝ)*X 2 1+(4297963561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2239147429/10000000000 : ℝ)*X 0 0+(5282409067/10000000000 : ℝ)*X 0 1+(1056481823/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5361891331/10000000000 : ℝ)*X 1 0+(-426696187/2000000000 : ℝ)*X 1 1+(1056481807/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5361891327/10000000000 : ℝ)*X 2 0+(5282409059/10000000000 : ℝ)*X 2 1+(-213348091/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242320101/10000000000 : ℝ)*X 0 0+(4404552191/10000000000 : ℝ)*X 0 1+(4404552187/10000000000 : ℝ)*X 0 2+(4242320101/10000000000 : ℝ)*X 1 0+(4404552191/10000000000 : ℝ)*X 1 1+(4404552187/10000000000 : ℝ)*X 1 2+(4242320101/10000000000 : ℝ)*X 2 0+(4404552191/10000000000 : ℝ)*X 2 1+(4404552187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-546791187/2500000000 : ℝ)*X 0 0+(2609731573/5000000000 : ℝ)*X 0 1+(1076854171/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322525517/2500000000 : ℝ)*X 1 0+(-523248919/2500000000 : ℝ)*X 1 1+(1346067629/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2645050893/5000000000 : ℝ)*X 2 0+(1076854229/2000000000 : ℝ)*X 2 1+(-418599041/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((179099303/400000000 : ℝ)*X 0 0+(2143425221/5000000000 : ℝ)*X 0 1+(4286850447/10000000000 : ℝ)*X 0 2+(179099303/400000000 : ℝ)*X 1 0+(2143425221/5000000000 : ℝ)*X 1 1+(4286850447/10000000000 : ℝ)*X 1 2+(179099303/400000000 : ℝ)*X 2 0+(2143425221/5000000000 : ℝ)*X 2 1+(4286850447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1021685879/5000000000 : ℝ)*X 0 0+(5436403593/10000000000 : ℝ)*X 0 1+(82411343/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((335474151/625000000 : ℝ)*X 1 0+(-534158081/2500000000 : ℝ)*X 1 1+(1318581369/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367586161/10000000000 : ℝ)*X 2 0+(5274325573/10000000000 : ℝ)*X 2 1+(-1068316269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((844681021/2000000000 : ℝ)*X 0 0+(4413886747/10000000000 : ℝ)*X 0 1+(2206943561/5000000000 : ℝ)*X 0 2+(844681021/2000000000 : ℝ)*X 1 0+(4413886747/10000000000 : ℝ)*X 1 1+(2206943561/5000000000 : ℝ)*X 1 2+(844681021/2000000000 : ℝ)*X 2 0+(4413886747/10000000000 : ℝ)*X 2 1+(2206943561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62249/100000 : ℝ) ≤ (-8481076038943030473941169944589/13625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11708191/100000000000000 : ℝ)*(lower0) + (11663461/50000000000000 : ℝ)*(lower2) + (2216141/10000000000000 : ℝ)*(lower3) + (21950907/100000000000000 : ℝ)*(lower4) + (1003306167422263/25000000000000 : ℝ)*(major0) + (1003306167422263/25000000000000 : ℝ)*(major1) + (1003306167422263/25000000000000 : ℝ)*(major2) + (57038661/2500000000000 : ℝ)*(sp1) + (1737578911/100000000000000 : ℝ)*(sp2) + (337566397371559/6250000000000 : ℝ)*(sp4) + (675132509549813/12500000000000 : ℝ)*(sp5) + (2700530310183017/50000000000000 : ℝ)*(sp6) + (2646131624818523/100000000000000 : ℝ)*(sp7) + (2083247917/50000000000000 : ℝ)*(sp15) + (1323067895657179/50000000000000 : ℝ)*(f.failure) + (337566397371559/6250000000000 : ℝ)*(f.sum) + (3557962886333/545000000000000000000000000 : ℝ)*base66 + (478454148810296621/27250000000000000000000000000000 : ℝ)*base67 + (129026827377796621/27250000000000000000000000000000 : ℝ)*base69 + (223947767494796621/27250000000000000000000000000000 : ℝ)*base71 + (814438177737/545000000000000000000000000 : ℝ)*base73 + (129725325537796621/27250000000000000000000000000000 : ℝ)*base75 + (35521461595296621/27250000000000000000000000000000 : ℝ)*base77 + (54989318141796621/27250000000000000000000000000000 : ℝ)*base79 + (2371817460707/545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10939701/1000000000000000000000 : ℝ)*base89 + (10939701/1000000000000000000000 : ℝ)*base91 + (10939701/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59387/100000 : ℝ) ≤ (4045916787246538901480676892119/6812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19917469/50000000000000 : ℝ)*(upper3) + (3926031/20000000000000 : ℝ)*(upper4) + (2683823/20000000000000 : ℝ)*(lower5) + (509903082647227/12500000000000 : ℝ)*(major0) + (509903082647227/12500000000000 : ℝ)*(major1) + (509903082647227/12500000000000 : ℝ)*(major2) + (1362249902302303/25000000000000 : ℝ)*(sp0) + (2724477949935781/50000000000000 : ℝ)*(sp1) + (340562217342757/6250000000000 : ℝ)*(sp2) + (2689645305729121/100000000000000 : ℝ)*(sp3) + (4159567573/100000000000000 : ℝ)*(sp6) + (27842473/100000000000000 : ℝ)*(sp8) + (43737180123/100000000000000 : ℝ)*(sp9) + (3922417997/50000000000000 : ℝ)*(sp11) + (1344826575282557/50000000000000 : ℝ)*(f.failure) + (1089799927410337/20000000000000 : ℝ)*(f.sum) + (940004192627/272500000000000000000000000 : ℝ)*base66 + (115155989780009209/13625000000000000000000000000000 : ℝ)*base67 + (82940978304009209/13625000000000000000000000000000 : ℝ)*base69 + (17585249471509209/13625000000000000000000000000000 : ℝ)*base71 + (5199831787/17031250000000000000000000 : ℝ)*base74 + (97708559154634209/13625000000000000000000000000000 : ℝ)*base75 + (93361597244134209/13625000000000000000000000000000 : ℝ)*base77 + (122252932242384209/13625000000000000000000000000000 : ℝ)*base79 + (1622444773311/545000000000000000000000000 : ℝ)*base81 + (12917517/1000000000000000000000 : ℝ)*base90 + (12917517/1000000000000000000000 : ℝ)*base92 + (12917517/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (5009/6250 : ℝ) ≤ (21839998429277516883468155902539/27250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65909781/25000000000000 : ℝ)*(lower3) + (29636139/25000000000000 : ℝ)*(upper4) + (142254381/100000000000000 : ℝ)*(lower5) + (4545882394690261/100000000000000 : ℝ)*(major0) + (4545882394690261/100000000000000 : ℝ)*(major1) + (4545882394690261/100000000000000 : ℝ)*(major2) + (1057960171/6250000000000 : ℝ)*(sp0) + (77209298237/100000000000000 : ℝ)*(sp1) + (31537182209/6250000000000 : ℝ)*(sp2) + (100596979947/50000000000000 : ℝ)*(sp3) + (758460808465223/12500000000000 : ℝ)*(sp8) + (6067626185786283/100000000000000 : ℝ)*(sp9) + (6067198800169177/100000000000000 : ℝ)*(sp10) + (374643075740899/12500000000000 : ℝ)*(sp11) + (1498672899943543/50000000000000 : ℝ)*(f.failure) + (6067703395084521/100000000000000 : ℝ)*(f.sum) + (3023261082209/545000000000000000000000000 : ℝ)*base66 + (1352653341301232487/109000000000000000000000000000000 : ℝ)*base67 + (2191869009527232487/109000000000000000000000000000000 : ℝ)*base69 + (878726116373232487/109000000000000000000000000000000 : ℝ)*base71 + (1341875538431/545000000000000000000000000 : ℝ)*base73 + (1838727700520232487/109000000000000000000000000000000 : ℝ)*base75 + (21242758028767513/109000000000000000000000000000000 : ℝ)*base78 + (1819410971656232487/109000000000000000000000000000000 : ℝ)*base79 + (1214901048143/272500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4316583/1000000000000000000000 : ℝ)*base90 + (4316583/1000000000000000000000 : ℝ)*base92 + (4316583/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-20843/25000 : ℝ) ≤ (-22718144826215114126986972862349/27250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6412541/20000000000000 : ℝ)*(upper3) + (21095783/10000000000000 : ℝ)*(lower4) + (2149613/5000000000000 : ℝ)*(upper5) + (4581459934542451/100000000000000 : ℝ)*(major0) + (4581459934542451/100000000000000 : ℝ)*(major1) + (4581459934542451/100000000000000 : ℝ)*(major2) + (7722507503/50000000000000 : ℝ)*(sp4) + (418422963477/100000000000000 : ℝ)*(sp5) + (128151527151/25000000000000 : ℝ)*(sp6) + (40306219613/20000000000000 : ℝ)*(sp7) + (6169890210110007/100000000000000 : ℝ)*(sp12) + (24099559500631/390625000000 : ℝ)*(sp13) + (771174131127051/12500000000000 : ℝ)*(sp14) + (3020602462465751/100000000000000 : ℝ)*(sp15) + (377600499195477/12500000000000 : ℝ)*(f.failure) + (1542476413781253/25000000000000 : ℝ)*(f.sum) + (1230348137659/545000000000000000000000000 : ℝ)*base66 + (194918769845520783/109000000000000000000000000000000 : ℝ)*base68 + (1510868266939520783/109000000000000000000000000000000 : ℝ)*base70 + (308011645507520783/109000000000000000000000000000000 : ℝ)*base72 + (39121968867/17031250000000000000000000 : ℝ)*base74 + (1134897234932520783/109000000000000000000000000000000 : ℝ)*base76 + (269119827804520783/109000000000000000000000000000000 : ℝ)*base78 + (121951765651479217/109000000000000000000000000000000 : ℝ)*base79 + (131876484793/68125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2411963/250000000000000000000 : ℝ)*base89 + (2411963/250000000000000000000 : ℝ)*base91 + (2411963/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1254_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59387/100000 : ℝ) else (5009/6250 : ℝ) ≤ X j i ∧ X j i ≤ (20843/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1254_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1254_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59387/100000 : ℝ) else (5009/6250 : ℝ) ≤ X j i ∧ X j i ≤ (20843/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1254_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1254_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59387/100000 : ℝ) else (5009/6250 : ℝ) ≤ X j i ∧ X j i ≤ (20843/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
