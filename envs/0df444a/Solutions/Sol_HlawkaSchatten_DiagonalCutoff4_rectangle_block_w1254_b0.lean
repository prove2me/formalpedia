-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:24:43.465644+00:00
-- url     : https://prove2.me/submissions/d93e4a67-7ba6-46d2-a20a-37498f5dffdb

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
theorem support_rectangle_w1254_s0_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1856863039/10000000000 : ℝ)*x 0 + (6028804703/10000000000 : ℝ)*x 1 + (479447181/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1856863039/10000000000 : ℝ)^8447 ≤ (2708275696739/25000000000000 : ℝ)^6399 := by
    have hnat : (1856863039 : ℕ)^8447*25000000000000^6399 ≤ 2708275696739^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856863039 10000000000 2708275696739 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6028804703/10000000000 : ℝ)^8447 ≤ (51273647623871/100000000000000 : ℝ)^6399 := by
    have hnat : (6028804703 : ℕ)^8447*100000000000000^6399 ≤ 51273647623871^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6028804703 10000000000 51273647623871 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479447181/1000000000 : ℝ)^8447 ≤ (2368328098317/6250000000000 : ℝ)^6399 := by
    have hnat : (479447181 : ℕ)^8447*6250000000000^6399 ≤ 2368328098317^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479447181 1000000000 2368328098317 6250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1856863039/10000000000 : ℝ), (6028804703/10000000000 : ℝ), (479447181/1000000000 : ℝ)] ![(2708275696739/25000000000000 : ℝ), (51273647623871/100000000000000 : ℝ), (2368328098317/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1856863039/10000000000 : ℝ)|^8447 ≤ (2708275696739/25000000000000 : ℝ)^6399
        have hw : |(-1856863039/10000000000 : ℝ)|=(1856863039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6028804703/10000000000 : ℝ)|^8447 ≤ (51273647623871/100000000000000 : ℝ)^6399
        have hw : |(6028804703/10000000000 : ℝ)|=(6028804703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(479447181/1000000000 : ℝ)|^8447 ≤ (2368328098317/6250000000000 : ℝ)^6399
        have hw : |(479447181/1000000000 : ℝ)|=(479447181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s0_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755241733/5000000000 : ℝ)*x 0 + (-2562179707/10000000000 : ℝ)*x 1 + (19177887/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755241733/5000000000 : ℝ)^8447 ≤ (45536271340181/100000000000000 : ℝ)^6399 := by
    have hnat : (2755241733 : ℕ)^8447*100000000000000^6399 ≤ 45536271340181^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755241733 5000000000 45536271340181 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562179707/10000000000 : ℝ)^8447 ≤ (16570479695947/100000000000000 : ℝ)^6399 := by
    have hnat : (2562179707 : ℕ)^8447*100000000000000^6399 ≤ 16570479695947^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562179707 10000000000 16570479695947 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19177887/40000000 : ℝ)^8447 ≤ (37893248947089/100000000000000 : ℝ)^6399 := by
    have hnat : (19177887 : ℕ)^8447*100000000000000^6399 ≤ 37893248947089^6399*40000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19177887 40000000 37893248947089 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755241733/5000000000 : ℝ), (-2562179707/10000000000 : ℝ), (19177887/40000000 : ℝ)] ![(45536271340181/100000000000000 : ℝ), (16570479695947/100000000000000 : ℝ), (37893248947089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755241733/5000000000 : ℝ)|^8447 ≤ (45536271340181/100000000000000 : ℝ)^6399
        have hw : |(2755241733/5000000000 : ℝ)|=(2755241733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2562179707/10000000000 : ℝ)|^8447 ≤ (16570479695947/100000000000000 : ℝ)^6399
        have hw : |(-2562179707/10000000000 : ℝ)|=(2562179707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19177887/40000000 : ℝ)|^8447 ≤ (37893248947089/100000000000000 : ℝ)^6399
        have hw : |(19177887/40000000 : ℝ)|=(19177887/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s0_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (275524171/500000000 : ℝ)*x 0 + (4794471823/10000000000 : ℝ)*x 1 + (-1281089839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275524171/500000000 : ℝ)^8447 ≤ (22768135419199/50000000000000 : ℝ)^6399 := by
    have hnat : (275524171 : ℕ)^8447*50000000000000^6399 ≤ 22768135419199^6399*500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275524171 500000000 22768135419199 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794471823/10000000000 : ℝ)^8447 ≤ (18946624854351/50000000000000 : ℝ)^6399 := by
    have hnat : (4794471823 : ℕ)^8447*50000000000000^6399 ≤ 18946624854351^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794471823 10000000000 18946624854351 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281089839/5000000000 : ℝ)^8447 ≤ (1035654965523/6250000000000 : ℝ)^6399 := by
    have hnat : (1281089839 : ℕ)^8447*6250000000000^6399 ≤ 1035654965523^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281089839 5000000000 1035654965523 6250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275524171/500000000 : ℝ), (4794471823/10000000000 : ℝ), (-1281089839/5000000000 : ℝ)] ![(22768135419199/50000000000000 : ℝ), (18946624854351/50000000000000 : ℝ), (1035654965523/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275524171/500000000 : ℝ)|^8447 ≤ (22768135419199/50000000000000 : ℝ)^6399
        have hw : |(275524171/500000000 : ℝ)|=(275524171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4794471823/10000000000 : ℝ)|^8447 ≤ (18946624854351/50000000000000 : ℝ)^6399
        have hw : |(4794471823/10000000000 : ℝ)|=(4794471823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1281089839/5000000000 : ℝ)|^8447 ≤ (1035654965523/6250000000000 : ℝ)^6399
        have hw : |(-1281089839/5000000000 : ℝ)|=(1281089839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s0_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (838416139/2000000000 : ℝ)*x 0 + (623289379/2000000000 : ℝ)*x 1 + (2813090633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838416139/2000000000 : ℝ)^8447 ≤ (6347726860673/20000000000000 : ℝ)^6399 := by
    have hnat : (838416139 : ℕ)^8447*20000000000000^6399 ≤ 6347726860673^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838416139 2000000000 6347726860673 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623289379/2000000000 : ℝ)^8447 ≤ (21458804527043/100000000000000 : ℝ)^6399 := by
    have hnat : (623289379 : ℕ)^8447*100000000000000^6399 ≤ 21458804527043^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623289379 2000000000 21458804527043 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2813090633/5000000000 : ℝ)^8447 ≤ (23401280582289/50000000000000 : ℝ)^6399 := by
    have hnat : (2813090633 : ℕ)^8447*50000000000000^6399 ≤ 23401280582289^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813090633 5000000000 23401280582289 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838416139/2000000000 : ℝ), (623289379/2000000000 : ℝ), (2813090633/5000000000 : ℝ)] ![(6347726860673/20000000000000 : ℝ), (21458804527043/100000000000000 : ℝ), (23401280582289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838416139/2000000000 : ℝ)|^8447 ≤ (6347726860673/20000000000000 : ℝ)^6399
        have hw : |(838416139/2000000000 : ℝ)|=(838416139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623289379/2000000000 : ℝ)|^8447 ≤ (21458804527043/100000000000000 : ℝ)^6399
        have hw : |(623289379/2000000000 : ℝ)|=(623289379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2813090633/5000000000 : ℝ)|^8447 ≤ (23401280582289/50000000000000 : ℝ)^6399
        have hw : |(2813090633/5000000000 : ℝ)|=(2813090633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s0_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-930843253/5000000000 : ℝ)*x 0 + (4826250623/10000000000 : ℝ)*x 1 + (1498975573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930843253/5000000000 : ℝ)^8447 ≤ (10870265128901/100000000000000 : ℝ)^6399 := by
    have hnat : (930843253 : ℕ)^8447*100000000000000^6399 ≤ 10870265128901^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930843253 5000000000 10870265128901 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826250623/10000000000 : ℝ)^8447 ≤ (19112575397221/50000000000000 : ℝ)^6399 := by
    have hnat : (4826250623 : ℕ)^8447*50000000000000^6399 ≤ 19112575397221^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826250623 10000000000 19112575397221 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498975573/2500000000 : ℝ)^8447 ≤ (25452292025457/50000000000000 : ℝ)^6399 := by
    have hnat : (1498975573 : ℕ)^8447*50000000000000^6399 ≤ 25452292025457^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498975573 2500000000 25452292025457 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-930843253/5000000000 : ℝ), (4826250623/10000000000 : ℝ), (1498975573/2500000000 : ℝ)] ![(10870265128901/100000000000000 : ℝ), (19112575397221/50000000000000 : ℝ), (25452292025457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-930843253/5000000000 : ℝ)|^8447 ≤ (10870265128901/100000000000000 : ℝ)^6399
        have hw : |(-930843253/5000000000 : ℝ)|=(930843253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826250623/10000000000 : ℝ)|^8447 ≤ (19112575397221/50000000000000 : ℝ)^6399
        have hw : |(4826250623/10000000000 : ℝ)|=(4826250623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498975573/2500000000 : ℝ)|^8447 ≤ (25452292025457/50000000000000 : ℝ)^6399
        have hw : |(1498975573/2500000000 : ℝ)|=(1498975573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s0_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174588763/10000000000 : ℝ)*x 0 + (-680373459/5000000000 : ℝ)*x 1 + (2997952331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174588763/10000000000 : ℝ)^8447 ≤ (41908469607473/100000000000000 : ℝ)^6399 := by
    have hnat : (5174588763 : ℕ)^8447*100000000000000^6399 ≤ 41908469607473^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174588763 10000000000 41908469607473 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680373459/5000000000 : ℝ)^8447 ≤ (3593459882709/50000000000000 : ℝ)^6399 := by
    have hnat : (680373459 : ℕ)^8447*50000000000000^6399 ≤ 3593459882709^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680373459 5000000000 3593459882709 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2997952331/5000000000 : ℝ)^8447 ≤ (50904610611711/100000000000000 : ℝ)^6399 := by
    have hnat : (2997952331 : ℕ)^8447*100000000000000^6399 ≤ 50904610611711^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997952331 5000000000 50904610611711 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174588763/10000000000 : ℝ), (-680373459/5000000000 : ℝ), (2997952331/5000000000 : ℝ)] ![(41908469607473/100000000000000 : ℝ), (3593459882709/50000000000000 : ℝ), (50904610611711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174588763/10000000000 : ℝ)|^8447 ≤ (41908469607473/100000000000000 : ℝ)^6399
        have hw : |(5174588763/10000000000 : ℝ)|=(5174588763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680373459/5000000000 : ℝ)|^8447 ≤ (3593459882709/50000000000000 : ℝ)^6399
        have hw : |(-680373459/5000000000 : ℝ)|=(680373459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2997952331/5000000000 : ℝ)|^8447 ≤ (50904610611711/100000000000000 : ℝ)^6399
        have hw : |(2997952331/5000000000 : ℝ)|=(2997952331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s0_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587294883/5000000000 : ℝ)*x 0 + (5995902719/10000000000 : ℝ)*x 1 + (-170093563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587294883/5000000000 : ℝ)^8447 ≤ (41908480330497/100000000000000 : ℝ)^6399 := by
    have hnat : (2587294883 : ℕ)^8447*100000000000000^6399 ≤ 41908480330497^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587294883 5000000000 41908480330497 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5995902719/10000000000 : ℝ)^8447 ≤ (2545229441817/5000000000000 : ℝ)^6399 := by
    have hnat : (5995902719 : ℕ)^8447*5000000000000^6399 ≤ 2545229441817^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5995902719 10000000000 2545229441817 5000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170093563/1250000000 : ℝ)^8447 ≤ (1796732705743/25000000000000 : ℝ)^6399 := by
    have hnat : (170093563 : ℕ)^8447*25000000000000^6399 ≤ 1796732705743^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170093563 1250000000 1796732705743 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587294883/5000000000 : ℝ), (5995902719/10000000000 : ℝ), (-170093563/1250000000 : ℝ)] ![(41908480330497/100000000000000 : ℝ), (2545229441817/5000000000000 : ℝ), (1796732705743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587294883/5000000000 : ℝ)|^8447 ≤ (41908480330497/100000000000000 : ℝ)^6399
        have hw : |(2587294883/5000000000 : ℝ)|=(2587294883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5995902719/10000000000 : ℝ)|^8447 ≤ (2545229441817/5000000000000 : ℝ)^6399
        have hw : |(5995902719/10000000000 : ℝ)|=(5995902719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170093563/1250000000 : ℝ)|^8447 ≤ (1796732705743/25000000000000 : ℝ)^6399
        have hw : |(-170093563/1250000000 : ℝ)|=(170093563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s0_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (420189003/1000000000 : ℝ)*x 0 + (5561571849/10000000000 : ℝ)*x 1 + (3183340511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420189003/1000000000 : ℝ)^8447 ≤ (15918353832113/50000000000000 : ℝ)^6399 := by
    have hnat : (420189003 : ℕ)^8447*50000000000000^6399 ≤ 15918353832113^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420189003 1000000000 15918353832113 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5561571849/10000000000 : ℝ)^8447 ≤ (11523596298821/25000000000000 : ℝ)^6399 := by
    have hnat : (5561571849 : ℕ)^8447*25000000000000^6399 ≤ 11523596298821^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5561571849 10000000000 11523596298821 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183340511/10000000000 : ℝ)^8447 ≤ (11034453565833/50000000000000 : ℝ)^6399 := by
    have hnat : (3183340511 : ℕ)^8447*50000000000000^6399 ≤ 11034453565833^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183340511 10000000000 11034453565833 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420189003/1000000000 : ℝ), (5561571849/10000000000 : ℝ), (3183340511/10000000000 : ℝ)] ![(15918353832113/50000000000000 : ℝ), (11523596298821/25000000000000 : ℝ), (11034453565833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420189003/1000000000 : ℝ)|^8447 ≤ (15918353832113/50000000000000 : ℝ)^6399
        have hw : |(420189003/1000000000 : ℝ)|=(420189003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5561571849/10000000000 : ℝ)|^8447 ≤ (11523596298821/25000000000000 : ℝ)^6399
        have hw : |(5561571849/10000000000 : ℝ)|=(5561571849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183340511/10000000000 : ℝ)|^8447 ≤ (11034453565833/50000000000000 : ℝ)^6399
        have hw : |(3183340511/10000000000 : ℝ)|=(3183340511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (433/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27391/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4223/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4223 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4223*1^1024 ≤ 0^1024*1^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4223/1024 : ℝ) ≤ (571249833097271829/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4223 ≤ (571249833097271829/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4223*25000000000000000000^1024 ≤ 571249833097271829^1024*5^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 571249833097271829 25000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (571249833097271829/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4223 := by
      have hnat : (1 : ℕ)^1024*1^4223 ≤ 1^4223*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25571249833097271829/25000000000000000000 : ℝ) ≤ (10054933831919913/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (25571249833097271829/25000000000000000000 : ℝ)^1024 ≤ (10054933831919913/10000000000000000 : ℝ)^4223 := by
      have hnat : (25571249833097271829 : ℕ)^1024*10000000000000000^4223 ≤ 10054933831919913^4223*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25571249833097271829 25000000000000000000 10054933831919913 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054933831919913/10000000000000000 : ℝ)) (X := (25571249833097271829/25000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13071249833097271829/12500000000000000000 : ℝ) ≤ (5054933831919913/5000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (13071249833097271829/12500000000000000000 : ℝ)^1024 ≤ (5054933831919913/5000000000000000 : ℝ)^4223 := by
      have hnat : (13071249833097271829 : ℕ)^1024*5000000000000000^4223 ≤ 5054933831919913^4223*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13071249833097271829 12500000000000000000 5054933831919913 5000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054933831919913/5000000000000000 : ℝ)) (X := (13071249833097271829/12500000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54933831919913/4000000000000000 : ℝ)*(0 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(54933831919913/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(571249833097271829/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54933831919913/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (1 : ℝ)+(54933831919913/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054933831919913/10000000000000000 : ℝ) by norm_num, show 1+(571249833097271829/25000000000000000000 : ℝ)+(0 : ℝ)=(25571249833097271829/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(571249833097271829/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54933831919913/4000000000000000 : ℝ)*(2/5 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(54933831919913/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054933831919913/5000000000000000 : ℝ) by norm_num, show 1+2*(571249833097271829/25000000000000000000 : ℝ)=(13071249833097271829/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54933831919913/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54933831919913/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54933831919913/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54933831919913/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54933831919913/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54933831919913/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1856863039/10000000000 : ℝ)*X 0 0+(6028804703/10000000000 : ℝ)*X 0 1+(479447181/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755241733/5000000000 : ℝ)*X 1 0+(-2562179707/10000000000 : ℝ)*X 1 1+(19177887/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((275524171/500000000 : ℝ)*X 2 0+(4794471823/10000000000 : ℝ)*X 2 1+(-1281089839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((838416139/2000000000 : ℝ)*X 0 0+(623289379/2000000000 : ℝ)*X 0 1+(2813090633/5000000000 : ℝ)*X 0 2+(838416139/2000000000 : ℝ)*X 1 0+(623289379/2000000000 : ℝ)*X 1 1+(2813090633/5000000000 : ℝ)*X 1 2+(838416139/2000000000 : ℝ)*X 2 0+(623289379/2000000000 : ℝ)*X 2 1+(2813090633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-930843253/5000000000 : ℝ)*X 0 0+(4826250623/10000000000 : ℝ)*X 0 1+(1498975573/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174588763/10000000000 : ℝ)*X 1 0+(-680373459/5000000000 : ℝ)*X 1 1+(2997952331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587294883/5000000000 : ℝ)*X 2 0+(5995902719/10000000000 : ℝ)*X 2 1+(-170093563/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((420189003/1000000000 : ℝ)*X 0 0+(5561571849/10000000000 : ℝ)*X 0 1+(3183340511/10000000000 : ℝ)*X 0 2+(420189003/1000000000 : ℝ)*X 1 0+(5561571849/10000000000 : ℝ)*X 1 1+(3183340511/10000000000 : ℝ)*X 1 2+(420189003/1000000000 : ℝ)*X 2 0+(5561571849/10000000000 : ℝ)*X 2 1+(3183340511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (288008028997908320039931/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39004711/100000000000000 : ℝ)*(base1) + (717507593/100000000000000 : ℝ)*(base19) + (132434337/20000000000000 : ℝ)*(base23) + (9714587/20000000000000 : ℝ)*(base24) + (156892571/100000000000000 : ℝ)*(upper3) + (604304424519157/100000000000000 : ℝ)*(major0) + (604304424519157/100000000000000 : ℝ)*(major1) + (604304424519157/100000000000000 : ℝ)*(major2) + (10126957972659/1250000000000 : ℝ)*(sp0) + (810157488104867/100000000000000 : ℝ)*(sp1) + (1265871085731/156250000000 : ℝ)*(sp2) + (199224637850239/50000000000000 : ℝ)*(sp3) + (401701113/25000000000000 : ℝ)*(sp4) + (616358989/50000000000000 : ℝ)*(sp7) + (6225789803487/1562500000000 : ℝ)*(f.failure) + (40507910280623/5000000000000 : ℝ)*(f.sum) + (654003006673341/200000000000000000000000000000 : ℝ)*base65 + (1007968003073341/400000000000000000000000000000 : ℝ)*base67 + (3523661522273341/400000000000000000000000000000 : ℝ)*base69 + (3417508929473341/400000000000000000000000000000 : ℝ)*base71 + (383216525673341/200000000000000000000000000000 : ℝ)*base73 + (2232869495873341/400000000000000000000000000000 : ℝ)*base75 + (964075418273341/400000000000000000000000000000 : ℝ)*base77 + (3201777377473341/400000000000000000000000000000 : ℝ)*base79 + (1640473881073341/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (171347/31250000000000000000 : ℝ)*base90 + (171347/31250000000000000000 : ℝ)*base92 + (171347/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136850871563050387827531/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169266647/100000000000000 : ℝ)*(base1) + (595227579/100000000000000 : ℝ)*(base19) + (359189943/50000000000000 : ℝ)*(base23) + (130135583/100000000000000 : ℝ)*(upper3) + (318859167070929/50000000000000 : ℝ)*(major0) + (318859167070929/50000000000000 : ℝ)*(major1) + (318859167070929/50000000000000 : ℝ)*(major2) + (1742359351/100000000000000 : ℝ)*(sp1) + (135829169/12500000000000 : ℝ)*(sp2) + (12816121/2500000000000 : ℝ)*(sp3) + (854954603491159/100000000000000 : ℝ)*(sp4) + (427476048318791/50000000000000 : ℝ)*(sp5) + (427476314605637/50000000000000 : ℝ)*(sp6) + (105120365228449/25000000000000 : ℝ)*(sp7) + (210241071412641/50000000000000 : ℝ)*(f.failure) + (6679331517379/781250000000 : ℝ)*(f.sum) + (134005004090823/100000000000000000000000000000 : ℝ)*base66 + (849111813690823/200000000000000000000000000000 : ℝ)*base68 + (620657993709177/200000000000000000000000000000 : ℝ)*base69 + (136876856109177/200000000000000000000000000000 : ℝ)*base71 + (348517098590823/100000000000000000000000000000 : ℝ)*base74 + (920583027490823/200000000000000000000000000000 : ℝ)*base76 + (561235962290823/200000000000000000000000000000 : ℝ)*base78 + (968982342690823/200000000000000000000000000000 : ℝ)*base80 + (363826474109177/100000000000000000000000000000 : ℝ)*base81 + (7499121/1000000000000000000000 : ℝ)*base90 + (7499121/1000000000000000000000 : ℝ)*base92 + (7499121/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1254_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (433/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27391/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1254_s1_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-513350799/2500000000 : ℝ)*x 0 + (5672596913/10000000000 : ℝ)*x 1 + (628108921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513350799/2500000000 : ℝ)^8447 ≤ (12371763424663/100000000000000 : ℝ)^6399 := by
    have hnat : (513350799 : ℕ)^8447*100000000000000^6399 ≤ 12371763424663^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513350799 2500000000 12371763424663 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5672596913/10000000000 : ℝ)^8447 ≤ (11828232045633/25000000000000 : ℝ)^6399 := by
    have hnat : (5672596913 : ℕ)^8447*25000000000000^6399 ≤ 11828232045633^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672596913 10000000000 11828232045633 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628108921/1250000000 : ℝ)^8447 ≤ (2519706774011/6250000000000 : ℝ)^6399 := by
    have hnat : (628108921 : ℕ)^8447*6250000000000^6399 ≤ 2519706774011^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628108921 1250000000 2519706774011 6250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513350799/2500000000 : ℝ), (5672596913/10000000000 : ℝ), (628108921/1250000000 : ℝ)] ![(12371763424663/100000000000000 : ℝ), (11828232045633/25000000000000 : ℝ), (2519706774011/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513350799/2500000000 : ℝ)|^8447 ≤ (12371763424663/100000000000000 : ℝ)^6399
        have hw : |(-513350799/2500000000 : ℝ)|=(513350799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5672596913/10000000000 : ℝ)|^8447 ≤ (11828232045633/25000000000000 : ℝ)^6399
        have hw : |(5672596913/10000000000 : ℝ)|=(5672596913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628108921/1250000000 : ℝ)|^8447 ≤ (2519706774011/6250000000000 : ℝ)^6399
        have hw : |(628108921/1250000000 : ℝ)|=(628108921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s1_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5413005259/10000000000 : ℝ)*x 0 + (-2401025131/10000000000 : ℝ)*x 1 + (502487157/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413005259/10000000000 : ℝ)^8447 ≤ (44475969379499/100000000000000 : ℝ)^6399 := by
    have hnat : (5413005259 : ℕ)^8447*100000000000000^6399 ≤ 44475969379499^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413005259 10000000000 44475969379499 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401025131/10000000000 : ℝ)^8447 ≤ (15208720076507/100000000000000 : ℝ)^6399 := by
    have hnat : (2401025131 : ℕ)^8447*100000000000000^6399 ≤ 15208720076507^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401025131 10000000000 15208720076507 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502487157/1000000000 : ℝ)^8447 ≤ (806306210471/2000000000000 : ℝ)^6399 := by
    have hnat : (502487157 : ℕ)^8447*2000000000000^6399 ≤ 806306210471^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502487157 1000000000 806306210471 2000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413005259/10000000000 : ℝ), (-2401025131/10000000000 : ℝ), (502487157/1000000000 : ℝ)] ![(44475969379499/100000000000000 : ℝ), (15208720076507/100000000000000 : ℝ), (806306210471/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413005259/10000000000 : ℝ)|^8447 ≤ (44475969379499/100000000000000 : ℝ)^6399
        have hw : |(5413005259/10000000000 : ℝ)|=(5413005259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2401025131/10000000000 : ℝ)|^8447 ≤ (15208720076507/100000000000000 : ℝ)^6399
        have hw : |(-2401025131/10000000000 : ℝ)|=(2401025131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502487157/1000000000 : ℝ)|^8447 ≤ (806306210471/2000000000000 : ℝ)^6399
        have hw : |(502487157/1000000000 : ℝ)|=(502487157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s1_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1353251361/2500000000 : ℝ)*x 0 + (2512435723/5000000000 : ℝ)*x 1 + (-2401025049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353251361/2500000000 : ℝ)^8447 ≤ (11118992846511/25000000000000 : ℝ)^6399 := by
    have hnat : (1353251361 : ℕ)^8447*25000000000000^6399 ≤ 11118992846511^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353251361 2500000000 11118992846511 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512435723/5000000000 : ℝ)^8447 ≤ (40315309210271/100000000000000 : ℝ)^6399 := by
    have hnat : (2512435723 : ℕ)^8447*100000000000000^6399 ≤ 40315309210271^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512435723 5000000000 40315309210271 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2401025049/10000000000 : ℝ)^8447 ≤ (760435969543/5000000000000 : ℝ)^6399 := by
    have hnat : (2401025049 : ℕ)^8447*5000000000000^6399 ≤ 760435969543^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401025049 10000000000 760435969543 5000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353251361/2500000000 : ℝ), (2512435723/5000000000 : ℝ), (-2401025049/10000000000 : ℝ)] ![(11118992846511/25000000000000 : ℝ), (40315309210271/100000000000000 : ℝ), (760435969543/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353251361/2500000000 : ℝ)|^8447 ≤ (11118992846511/25000000000000 : ℝ)^6399
        have hw : |(1353251361/2500000000 : ℝ)|=(1353251361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512435723/5000000000 : ℝ)|^8447 ≤ (40315309210271/100000000000000 : ℝ)^6399
        have hw : |(2512435723/5000000000 : ℝ)|=(2512435723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2401025049/10000000000 : ℝ)|^8447 ≤ (760435969543/5000000000000 : ℝ)^6399
        have hw : |(-2401025049/10000000000 : ℝ)|=(2401025049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s1_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4307814201/10000000000 : ℝ)*x 0 + (739524347/2000000000 : ℝ)*x 1 + (1002924871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307814201/10000000000 : ℝ)^8447 ≤ (16450189540393/50000000000000 : ℝ)^6399 := by
    have hnat : (4307814201 : ℕ)^8447*50000000000000^6399 ≤ 16450189540393^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307814201 10000000000 16450189540393 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739524347/2000000000 : ℝ)^8447 ≤ (13446401411057/50000000000000 : ℝ)^6399 := by
    have hnat : (739524347 : ℕ)^8447*50000000000000^6399 ≤ 13446401411057^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739524347 2000000000 13446401411057 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002924871/2000000000 : ℝ)^8447 ≤ (20103409043899/50000000000000 : ℝ)^6399 := by
    have hnat : (1002924871 : ℕ)^8447*50000000000000^6399 ≤ 20103409043899^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002924871 2000000000 20103409043899 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307814201/10000000000 : ℝ), (739524347/2000000000 : ℝ), (1002924871/2000000000 : ℝ)] ![(16450189540393/50000000000000 : ℝ), (13446401411057/50000000000000 : ℝ), (20103409043899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307814201/10000000000 : ℝ)|^8447 ≤ (16450189540393/50000000000000 : ℝ)^6399
        have hw : |(4307814201/10000000000 : ℝ)|=(4307814201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(739524347/2000000000 : ℝ)|^8447 ≤ (13446401411057/50000000000000 : ℝ)^6399
        have hw : |(739524347/2000000000 : ℝ)|=(739524347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002924871/2000000000 : ℝ)|^8447 ≤ (20103409043899/50000000000000 : ℝ)^6399
        have hw : |(1002924871/2000000000 : ℝ)|=(1002924871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s1_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027032637/5000000000 : ℝ)*x 0 + (5033339681/10000000000 : ℝ)*x 1 + (5663968333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027032637/5000000000 : ℝ)^8447 ≤ (1547128675757/12500000000000 : ℝ)^6399 := by
    have hnat : (1027032637 : ℕ)^8447*12500000000000^6399 ≤ 1547128675757^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027032637 5000000000 1547128675757 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5033339681/10000000000 : ℝ)^8447 ≤ (40405020146111/100000000000000 : ℝ)^6399 := by
    have hnat : (5033339681 : ℕ)^8447*100000000000000^6399 ≤ 40405020146111^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033339681 10000000000 40405020146111 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5663968333/10000000000 : ℝ)^8447 ≤ (47217950437493/100000000000000 : ℝ)^6399 := by
    have hnat : (5663968333 : ℕ)^8447*100000000000000^6399 ≤ 47217950437493^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663968333 10000000000 47217950437493 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027032637/5000000000 : ℝ), (5033339681/10000000000 : ℝ), (5663968333/10000000000 : ℝ)] ![(1547128675757/12500000000000 : ℝ), (40405020146111/100000000000000 : ℝ), (47217950437493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027032637/5000000000 : ℝ)|^8447 ≤ (1547128675757/12500000000000 : ℝ)^6399
        have hw : |(-1027032637/5000000000 : ℝ)|=(1027032637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5033339681/10000000000 : ℝ)|^8447 ≤ (40405020146111/100000000000000 : ℝ)^6399
        have hw : |(5033339681/10000000000 : ℝ)|=(5033339681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5663968333/10000000000 : ℝ)|^8447 ≤ (47217950437493/100000000000000 : ℝ)^6399
        have hw : |(5663968333/10000000000 : ℝ)|=(5663968333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s1_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246037973/10000000000 : ℝ)*x 0 + (-880964039/5000000000 : ℝ)*x 1 + (1132793731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246037973/10000000000 : ℝ)^8447 ≤ (21337006088797/50000000000000 : ℝ)^6399 := by
    have hnat : (5246037973 : ℕ)^8447*50000000000000^6399 ≤ 21337006088797^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246037973 10000000000 21337006088797 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880964039/5000000000 : ℝ)^8447 ≤ (5054016912083/50000000000000 : ℝ)^6399 := by
    have hnat : (880964039 : ℕ)^8447*50000000000000^6399 ≤ 5054016912083^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880964039 5000000000 5054016912083 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132793731/2000000000 : ℝ)^8447 ≤ (23608976990497/50000000000000 : ℝ)^6399 := by
    have hnat : (1132793731 : ℕ)^8447*50000000000000^6399 ≤ 23608976990497^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132793731 2000000000 23608976990497 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246037973/10000000000 : ℝ), (-880964039/5000000000 : ℝ), (1132793731/2000000000 : ℝ)] ![(21337006088797/50000000000000 : ℝ), (5054016912083/50000000000000 : ℝ), (23608976990497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246037973/10000000000 : ℝ)|^8447 ≤ (21337006088797/50000000000000 : ℝ)^6399
        have hw : |(5246037973/10000000000 : ℝ)|=(5246037973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-880964039/5000000000 : ℝ)|^8447 ≤ (5054016912083/50000000000000 : ℝ)^6399
        have hw : |(-880964039/5000000000 : ℝ)|=(880964039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132793731/2000000000 : ℝ)|^8447 ≤ (23608976990497/50000000000000 : ℝ)^6399
        have hw : |(1132793731/2000000000 : ℝ)|=(1132793731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s1_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (655754737/1250000000 : ℝ)*x 0 + (5663968427/10000000000 : ℝ)*x 1 + (-44048213/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655754737/1250000000 : ℝ)^8447 ≤ (42674011350769/100000000000000 : ℝ)^6399 := by
    have hnat : (655754737 : ℕ)^8447*100000000000000^6399 ≤ 42674011350769^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655754737 1250000000 42674011350769 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5663968427/10000000000 : ℝ)^8447 ≤ (47217951471931/100000000000000 : ℝ)^6399 := by
    have hnat : (5663968427 : ℕ)^8447*100000000000000^6399 ≤ 47217951471931^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663968427 10000000000 47217951471931 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44048213/250000000 : ℝ)^8447 ≤ (10108037171439/100000000000000 : ℝ)^6399 := by
    have hnat : (44048213 : ℕ)^8447*100000000000000^6399 ≤ 10108037171439^6399*250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44048213 250000000 10108037171439 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655754737/1250000000 : ℝ), (5663968427/10000000000 : ℝ), (-44048213/250000000 : ℝ)] ![(42674011350769/100000000000000 : ℝ), (47217951471931/100000000000000 : ℝ), (10108037171439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655754737/1250000000 : ℝ)|^8447 ≤ (42674011350769/100000000000000 : ℝ)^6399
        have hw : |(655754737/1250000000 : ℝ)|=(655754737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5663968427/10000000000 : ℝ)|^8447 ≤ (47217951471931/100000000000000 : ℝ)^6399
        have hw : |(5663968427/10000000000 : ℝ)|=(5663968427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44048213/250000000 : ℝ)|^8447 ≤ (10108037171439/100000000000000 : ℝ)^6399
        have hw : |(-44048213/250000000 : ℝ)|=(44048213/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s1_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4309160197/10000000000 : ℝ)*x 0 + (4997406127/10000000000 : ℝ)*x 1 + (928791559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309160197/10000000000 : ℝ)^8447 ≤ (32913949704373/100000000000000 : ℝ)^6399 := by
    have hnat : (4309160197 : ℕ)^8447*100000000000000^6399 ≤ 32913949704373^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309160197 10000000000 32913949704373 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997406127/10000000000 : ℝ)^8447 ≤ (40024679796649/100000000000000 : ℝ)^6399 := by
    have hnat : (4997406127 : ℕ)^8447*100000000000000^6399 ≤ 40024679796649^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997406127 10000000000 40024679796649 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928791559/2500000000 : ℝ)^8447 ≤ (1082454819421/4000000000000 : ℝ)^6399 := by
    have hnat : (928791559 : ℕ)^8447*4000000000000^6399 ≤ 1082454819421^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928791559 2500000000 1082454819421 4000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309160197/10000000000 : ℝ), (4997406127/10000000000 : ℝ), (928791559/2500000000 : ℝ)] ![(32913949704373/100000000000000 : ℝ), (40024679796649/100000000000000 : ℝ), (1082454819421/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309160197/10000000000 : ℝ)|^8447 ≤ (32913949704373/100000000000000 : ℝ)^6399
        have hw : |(4309160197/10000000000 : ℝ)|=(4309160197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997406127/10000000000 : ℝ)|^8447 ≤ (40024679796649/100000000000000 : ℝ)^6399
        have hw : |(4997406127/10000000000 : ℝ)|=(4997406127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(928791559/2500000000 : ℝ)|^8447 ≤ (1082454819421/4000000000000 : ℝ)^6399
        have hw : |(928791559/2500000000 : ℝ)|=(928791559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27391/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3127/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4987/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27391/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (433/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27391/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (433/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27391/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (433/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27391/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (433/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27391/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (433/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27391/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (433/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (433/50000 : ℝ) ^ (4223/1024 : ℝ) ≤ (156043416919/50000000000000000000 : ℝ) := by
    have hpowers : (433/50000 : ℝ)^4223 ≤ (156043416919/50000000000000000000 : ℝ)^1024 := by
      have hnat : (433 : ℕ)^4223*50000000000000000000^1024 ≤ 156043416919^1024*50000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        433 50000 156043416919 50000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (433/50000 : ℝ)) (X := (156043416919/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27391/100000 : ℝ) ^ (4223/1024 : ℝ) ≤ (479382028401982221/100000000000000000000 : ℝ) := by
    have hpowers : (27391/100000 : ℝ)^4223 ≤ (479382028401982221/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27391 : ℕ)^4223*100000000000000000000^1024 ≤ 479382028401982221^1024*100000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27391 100000 479382028401982221 100000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27391/100000 : ℝ)) (X := (479382028401982221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000156043416919/25000000000000000000 : ℝ) ≤ (5000000007567533/5000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (25000000156043416919/25000000000000000000 : ℝ)^1024 ≤ (5000000007567533/5000000000000000 : ℝ)^4223 := by
      have hnat : (25000000156043416919 : ℕ)^1024*5000000000000000^4223 ≤ 5000000007567533^4223*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000156043416919 25000000000000000000 5000000007567533 5000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000007567533/5000000000000000 : ℝ)) (X := (25000000156043416919/25000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100479382340488816059/100000000000000000000 : ℝ) ≤ (10011603095071043/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (100479382340488816059/100000000000000000000 : ℝ)^1024 ≤ (10011603095071043/10000000000000000 : ℝ)^4223 := by
      have hnat : (100479382340488816059 : ℕ)^1024*10000000000000000^4223 ≤ 10011603095071043^4223*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100479382340488816059 100000000000000000000 10011603095071043 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011603095071043/10000000000000000 : ℝ)) (X := (100479382340488816059/100000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50479382028401982221/50000000000000000000 : ℝ) ≤ (501160308750351/500000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50479382028401982221/50000000000000000000 : ℝ)^1024 ≤ (501160308750351/500000000000000 : ℝ)^4223 := by
      have hnat : (50479382028401982221 : ℕ)^1024*500000000000000^4223 ≤ 501160308750351^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50479382028401982221 50000000000000000000 501160308750351 500000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501160308750351/500000000000000 : ℝ)) (X := (50479382028401982221/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(156043416919/50000000000000000000 : ℝ) ≤ ((132614951933504256743/132625000000000000000 : ℝ)+2*(11603079935977/2652500000000000 : ℝ)*(433/50000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (132614951933504256743/132625000000000000000 : ℝ)+2*(11603079935977/2652500000000000 : ℝ)*(433/50000 : ℝ)=(5000000007567533/5000000000000000 : ℝ) by norm_num, show 1+2*(156043416919/50000000000000000000 : ℝ)=(25000000156043416919/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(479382028401982221/100000000000000000000 : ℝ)+(156043416919/50000000000000000000 : ℝ) ≤ ((132614951933504256743/132625000000000000000 : ℝ)+(11603079935977/2652500000000000 : ℝ)*((27391/100000 : ℝ)+(433/50000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (132614951933504256743/132625000000000000000 : ℝ)+(11603079935977/2652500000000000 : ℝ)*((27391/100000 : ℝ)+(433/50000 : ℝ))=(10011603095071043/10000000000000000 : ℝ) by norm_num, show 1+(479382028401982221/100000000000000000000 : ℝ)+(156043416919/50000000000000000000 : ℝ)=(100479382340488816059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(479382028401982221/100000000000000000000 : ℝ) ≤ ((132614951933504256743/132625000000000000000 : ℝ)+2*(11603079935977/2652500000000000 : ℝ)*(27391/100000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (132614951933504256743/132625000000000000000 : ℝ)+2*(11603079935977/2652500000000000 : ℝ)*(27391/100000 : ℝ)=(501160308750351/500000000000000 : ℝ) by norm_num, show 1+2*(479382028401982221/100000000000000000000 : ℝ)=(50479382028401982221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (132614951933504256743/132625000000000000000 : ℝ)*(X 1 0+X 2 0)+(11603079935977/2652500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (433/50000 : ℝ)) (hi := (27391/100000 : ℝ)) (c := (132614951933504256743/132625000000000000000 : ℝ)) (alpha := (11603079935977/2652500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (132614951933504256743/132625000000000000000 : ℝ)*(X 0 1+X 2 1)+(11603079935977/2652500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (433/50000 : ℝ)) (hi := (27391/100000 : ℝ)) (c := (132614951933504256743/132625000000000000000 : ℝ)) (alpha := (11603079935977/2652500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (132614951933504256743/132625000000000000000 : ℝ)*(X 0 2+X 1 2)+(11603079935977/2652500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (433/50000 : ℝ)) (hi := (27391/100000 : ℝ)) (c := (132614951933504256743/132625000000000000000 : ℝ)) (alpha := (11603079935977/2652500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-513350799/2500000000 : ℝ)*X 0 0+(5672596913/10000000000 : ℝ)*X 0 1+(628108921/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5413005259/10000000000 : ℝ)*X 1 0+(-2401025131/10000000000 : ℝ)*X 1 1+(502487157/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353251361/2500000000 : ℝ)*X 2 0+(2512435723/5000000000 : ℝ)*X 2 1+(-2401025049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307814201/10000000000 : ℝ)*X 0 0+(739524347/2000000000 : ℝ)*X 0 1+(1002924871/2000000000 : ℝ)*X 0 2+(4307814201/10000000000 : ℝ)*X 1 0+(739524347/2000000000 : ℝ)*X 1 1+(1002924871/2000000000 : ℝ)*X 1 2+(4307814201/10000000000 : ℝ)*X 2 0+(739524347/2000000000 : ℝ)*X 2 1+(1002924871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1027032637/5000000000 : ℝ)*X 0 0+(5033339681/10000000000 : ℝ)*X 0 1+(5663968333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246037973/10000000000 : ℝ)*X 1 0+(-880964039/5000000000 : ℝ)*X 1 1+(1132793731/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((655754737/1250000000 : ℝ)*X 2 0+(5663968427/10000000000 : ℝ)*X 2 1+(-44048213/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309160197/10000000000 : ℝ)*X 0 0+(4997406127/10000000000 : ℝ)*X 0 1+(928791559/2500000000 : ℝ)*X 0 2+(4309160197/10000000000 : ℝ)*X 1 0+(4997406127/10000000000 : ℝ)*X 1 1+(928791559/2500000000 : ℝ)*X 1 2+(4309160197/10000000000 : ℝ)*X 2 0+(4997406127/10000000000 : ℝ)*X 2 1+(928791559/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4713528332077063026565828251/1326250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14392559/50000000000000 : ℝ)*(base1) + (408400201/50000000000000 : ℝ)*(base19) + (869565263/100000000000000 : ℝ)*(base23) + (82851387/100000000000000 : ℝ)*(upper3) + (25504681/20000000000000 : ℝ)*(upper5) + (230317891366373/20000000000000 : ℝ)*(major0) + (230317891366373/20000000000000 : ℝ)*(major1) + (230317891366373/20000000000000 : ℝ)*(major2) + (1543868370456727/100000000000000 : ℝ)*(sp0) + (1543872848623601/100000000000000 : ℝ)*(sp1) + (77193639792937/5000000000000 : ℝ)*(sp2) + (151860511284029/20000000000000 : ℝ)*(sp3) + (1064750479/20000000000000 : ℝ)*(sp4) + (636141723/25000000000000 : ℝ)*(sp7) + (151861025954431/20000000000000 : ℝ)*(f.failure) + (1543873665424003/100000000000000 : ℝ)*(f.sum) + (6128977076123/13262500000000000000000000000 : ℝ)*base65 + (14177420395622746861/2652500000000000000000000000000000 : ℝ)*base68 + (17061540549705246861/2652500000000000000000000000000000 : ℝ)*base70 + (17046167906380246861/2652500000000000000000000000000000 : ℝ)*base72 + (91654282256221/26525000000000000000000000000 : ℝ)*base73 + (344752130802746861/2652500000000000000000000000000000 : ℝ)*base76 + (9487770751282746861/2652500000000000000000000000000000 : ℝ)*base78 + (9198593795457746861/2652500000000000000000000000000000 : ℝ)*base80 + (31230041071373/13262500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2327889/400000000000000000000 : ℝ)*base89 + (2327889/400000000000000000000 : ℝ)*base91 + (2327889/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1370492950490892954631542603/207226562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (38354223/100000000000000 : ℝ)*(base1) + (159285471/12500000000000 : ℝ)*(base19) + (305406349/25000000000000 : ℝ)*(base23) + (171768511/100000000000000 : ℝ)*(upper3) + (5749831/4000000000000 : ℝ)*(upper5) + (36962568183419/3125000000000 : ℝ)*(major0) + (36962568183419/3125000000000 : ℝ)*(major1) + (36962568183419/3125000000000 : ℝ)*(major2) + (3208443361/50000000000000 : ℝ)*(sp1) + (2746828959/50000000000000 : ℝ)*(sp2) + (1585718816358487/100000000000000 : ℝ)*(sp4) + (792855543416887/50000000000000 : ℝ)*(sp5) + (31714241254419/2000000000000 : ℝ)*(sp6) + (97485665866289/12500000000000 : ℝ)*(sp7) + (155977073056907/20000000000000 : ℝ)*(f.failure) + (198214847250533/12500000000000 : ℝ)*(f.sum) + (101645220034183/66312500000000000000000000000 : ℝ)*base65 + (1252141003503551279/207226562500000000000000000000000 : ℝ)*base68 + (1616796245193395029/207226562500000000000000000000000 : ℝ)*base70 + (1944943651098118183/414453125000000000000000000000000 : ℝ)*base72 + (102464233483567/66312500000000000000000000000 : ℝ)*base74 + (612530972683274433/414453125000000000000000000000000 : ℝ)*base76 + (1466107592196555683/414453125000000000000000000000000 : ℝ)*base78 + (938988885636399433/414453125000000000000000000000000 : ℝ)*base80 + (92275913344817/66312500000000000000000000000 : ℝ)*base82 + (959867/400000000000000000000 : ℝ)*base90 + (959867/400000000000000000000 : ℝ)*base92 + (959867/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1254_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27391/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3127/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4987/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1254_s2_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050423393/5000000000 : ℝ)*x 0 + (219630213/400000000 : ℝ)*x 1 + (5176445543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050423393/5000000000 : ℝ)^8447 ≤ (12750484770011/100000000000000 : ℝ)^6399 := by
    have hnat : (1050423393 : ℕ)^8447*100000000000000^6399 ≤ 12750484770011^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050423393 5000000000 12750484770011 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219630213/400000000 : ℝ)^8447 ≤ (45321193718307/100000000000000 : ℝ)^6399 := by
    have hnat : (219630213 : ℕ)^8447*100000000000000^6399 ≤ 45321193718307^6399*400000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219630213 400000000 45321193718307 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176445543/10000000000 : ℝ)^8447 ≤ (41928321491491/100000000000000 : ℝ)^6399 := by
    have hnat : (5176445543 : ℕ)^8447*100000000000000^6399 ≤ 41928321491491^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176445543 10000000000 41928321491491 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050423393/5000000000 : ℝ), (219630213/400000000 : ℝ), (5176445543/10000000000 : ℝ)] ![(12750484770011/100000000000000 : ℝ), (45321193718307/100000000000000 : ℝ), (41928321491491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050423393/5000000000 : ℝ)|^8447 ≤ (12750484770011/100000000000000 : ℝ)^6399
        have hw : |(-1050423393/5000000000 : ℝ)|=(1050423393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219630213/400000000 : ℝ)|^8447 ≤ (45321193718307/100000000000000 : ℝ)^6399
        have hw : |(219630213/400000000 : ℝ)|=(219630213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176445543/10000000000 : ℝ)|^8447 ≤ (41928321491491/100000000000000 : ℝ)^6399
        have hw : |(5176445543/10000000000 : ℝ)|=(5176445543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s2_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536920003/1000000000 : ℝ)*x 0 + (-2263589359/10000000000 : ℝ)*x 1 + (2588222829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536920003/1000000000 : ℝ)^8447 ≤ (22000732899941/50000000000000 : ℝ)^6399 := by
    have hnat : (536920003 : ℕ)^8447*50000000000000^6399 ≤ 22000732899941^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536920003 1000000000 22000732899941 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263589359/10000000000 : ℝ)^8447 ≤ (140702114611/1000000000000 : ℝ)^6399 := by
    have hnat : (2263589359 : ℕ)^8447*1000000000000^6399 ≤ 140702114611^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263589359 10000000000 140702114611 1000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588222829/5000000000 : ℝ)^8447 ≤ (10482080680273/25000000000000 : ℝ)^6399 := by
    have hnat : (2588222829 : ℕ)^8447*25000000000000^6399 ≤ 10482080680273^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588222829 5000000000 10482080680273 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536920003/1000000000 : ℝ), (-2263589359/10000000000 : ℝ), (2588222829/5000000000 : ℝ)] ![(22000732899941/50000000000000 : ℝ), (140702114611/1000000000000 : ℝ), (10482080680273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536920003/1000000000 : ℝ)|^8447 ≤ (22000732899941/50000000000000 : ℝ)^6399
        have hw : |(536920003/1000000000 : ℝ)|=(536920003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263589359/10000000000 : ℝ)|^8447 ≤ (140702114611/1000000000000 : ℝ)^6399
        have hw : |(-2263589359/10000000000 : ℝ)|=(2263589359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588222829/5000000000 : ℝ)|^8447 ≤ (10482080680273/25000000000000 : ℝ)^6399
        have hw : |(2588222829/5000000000 : ℝ)|=(2588222829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s2_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369199927/10000000000 : ℝ)*x 0 + (2588222859/5000000000 : ℝ)*x 1 + (-2263589417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369199927/10000000000 : ℝ)^8447 ≤ (70402343497/160000000000 : ℝ)^6399 := by
    have hnat : (5369199927 : ℕ)^8447*160000000000^6399 ≤ 70402343497^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369199927 10000000000 70402343497 160000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588222859/5000000000 : ℝ)^8447 ≤ (41928323362623/100000000000000 : ℝ)^6399 := by
    have hnat : (2588222859 : ℕ)^8447*100000000000000^6399 ≤ 41928323362623^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588222859 5000000000 41928323362623 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263589417/10000000000 : ℝ)^8447 ≤ (14070211937007/100000000000000 : ℝ)^6399 := by
    have hnat : (2263589417 : ℕ)^8447*100000000000000^6399 ≤ 14070211937007^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263589417 10000000000 14070211937007 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369199927/10000000000 : ℝ), (2588222859/5000000000 : ℝ), (-2263589417/10000000000 : ℝ)] ![(70402343497/160000000000 : ℝ), (41928323362623/100000000000000 : ℝ), (14070211937007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369199927/10000000000 : ℝ)|^8447 ≤ (70402343497/160000000000 : ℝ)^6399
        have hw : |(5369199927/10000000000 : ℝ)|=(5369199927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588222859/5000000000 : ℝ)|^8447 ≤ (41928323362623/100000000000000 : ℝ)^6399
        have hw : |(2588222859/5000000000 : ℝ)|=(2588222859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2263589417/10000000000 : ℝ)|^8447 ≤ (14070211937007/100000000000000 : ℝ)^6399
        have hw : |(-2263589417/10000000000 : ℝ)|=(2263589417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s2_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4340610461/10000000000 : ℝ)*x 0 + (2016216757/5000000000 : ℝ)*x 1 + (1167877599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340610461/10000000000 : ℝ)^8447 ≤ (33231423685471/100000000000000 : ℝ)^6399 := by
    have hnat : (4340610461 : ℕ)^8447*100000000000000^6399 ≤ 33231423685471^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340610461 10000000000 33231423685471 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016216757/5000000000 : ℝ)^8447 ≤ (3769111739821/12500000000000 : ℝ)^6399 := by
    have hnat : (2016216757 : ℕ)^8447*12500000000000^6399 ≤ 3769111739821^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016216757 5000000000 3769111739821 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167877599/2500000000 : ℝ)^8447 ≤ (18307841192583/50000000000000 : ℝ)^6399 := by
    have hnat : (1167877599 : ℕ)^8447*50000000000000^6399 ≤ 18307841192583^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167877599 2500000000 18307841192583 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340610461/10000000000 : ℝ), (2016216757/5000000000 : ℝ), (1167877599/2500000000 : ℝ)] ![(33231423685471/100000000000000 : ℝ), (3769111739821/12500000000000 : ℝ), (18307841192583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340610461/10000000000 : ℝ)|^8447 ≤ (33231423685471/100000000000000 : ℝ)^6399
        have hw : |(4340610461/10000000000 : ℝ)|=(4340610461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016216757/5000000000 : ℝ)|^8447 ≤ (3769111739821/12500000000000 : ℝ)^6399
        have hw : |(2016216757/5000000000 : ℝ)|=(2016216757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1167877599/2500000000 : ℝ)|^8447 ≤ (18307841192583/50000000000000 : ℝ)^6399
        have hw : |(1167877599/2500000000 : ℝ)|=(1167877599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s2_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100922741/10000000000 : ℝ)*x 0 + (5178449389/10000000000 : ℝ)*x 1 + (5488732839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100922741/10000000000 : ℝ)^8447 ≤ (12751093299433/100000000000000 : ℝ)^6399 := by
    have hnat : (2100922741 : ℕ)^8447*100000000000000^6399 ≤ 12751093299433^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100922741 10000000000 12751093299433 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178449389/10000000000 : ℝ)^8447 ≤ (41949748298269/100000000000000 : ℝ)^6399 := by
    have hnat : (5178449389 : ℕ)^8447*100000000000000^6399 ≤ 41949748298269^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178449389 10000000000 41949748298269 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488732839/10000000000 : ℝ)^8447 ≤ (1415598699641/3125000000000 : ℝ)^6399 := by
    have hnat : (5488732839 : ℕ)^8447*3125000000000^6399 ≤ 1415598699641^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488732839 10000000000 1415598699641 3125000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100922741/10000000000 : ℝ), (5178449389/10000000000 : ℝ), (5488732839/10000000000 : ℝ)] ![(12751093299433/100000000000000 : ℝ), (41949748298269/100000000000000 : ℝ), (1415598699641/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100922741/10000000000 : ℝ)|^8447 ≤ (12751093299433/100000000000000 : ℝ)^6399
        have hw : |(-2100922741/10000000000 : ℝ)|=(2100922741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178449389/10000000000 : ℝ)|^8447 ≤ (41949748298269/100000000000000 : ℝ)^6399
        have hw : |(5178449389/10000000000 : ℝ)|=(5178449389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488732839/10000000000 : ℝ)|^8447 ≤ (1415598699641/3125000000000 : ℝ)^6399
        have hw : |(5488732839/10000000000 : ℝ)|=(5488732839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s2_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057774807/2000000000 : ℝ)*x 0 + (-975650963/5000000000 : ℝ)*x 1 + (1372183221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057774807/2000000000 : ℝ)^8447 ≤ (4313458470933/10000000000000 : ℝ)^6399 := by
    have hnat : (1057774807 : ℕ)^8447*10000000000000^6399 ≤ 4313458470933^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057774807 2000000000 4313458470933 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975650963/5000000000 : ℝ)^8447 ≤ (11566256395601/100000000000000 : ℝ)^6399 := by
    have hnat : (975650963 : ℕ)^8447*100000000000000^6399 ≤ 11566256395601^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975650963 5000000000 11566256395601 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372183221/2500000000 : ℝ)^8447 ≤ (22649579439383/50000000000000 : ℝ)^6399 := by
    have hnat : (1372183221 : ℕ)^8447*50000000000000^6399 ≤ 22649579439383^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372183221 2500000000 22649579439383 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057774807/2000000000 : ℝ), (-975650963/5000000000 : ℝ), (1372183221/2500000000 : ℝ)] ![(4313458470933/10000000000000 : ℝ), (11566256395601/100000000000000 : ℝ), (22649579439383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057774807/2000000000 : ℝ)|^8447 ≤ (4313458470933/10000000000000 : ℝ)^6399
        have hw : |(1057774807/2000000000 : ℝ)|=(1057774807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-975650963/5000000000 : ℝ)|^8447 ≤ (11566256395601/100000000000000 : ℝ)^6399
        have hw : |(-975650963/5000000000 : ℝ)|=(975650963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372183221/2500000000 : ℝ)|^8447 ≤ (22649579439383/50000000000000 : ℝ)^6399
        have hw : |(1372183221/2500000000 : ℝ)|=(1372183221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s2_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288874179/10000000000 : ℝ)*x 0 + (1097746597/2000000000 : ℝ)*x 1 + (-487825397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288874179/10000000000 : ℝ)^8447 ≤ (10783646564907/25000000000000 : ℝ)^6399 := by
    have hnat : (5288874179 : ℕ)^8447*25000000000000^6399 ≤ 10783646564907^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288874179 10000000000 10783646564907 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097746597/2000000000 : ℝ)^8447 ≤ (45299159979113/100000000000000 : ℝ)^6399 := by
    have hnat : (1097746597 : ℕ)^8447*100000000000000^6399 ≤ 45299159979113^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097746597 2000000000 45299159979113 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487825397/2500000000 : ℝ)^8447 ≤ (11566253750907/100000000000000 : ℝ)^6399 := by
    have hnat : (487825397 : ℕ)^8447*100000000000000^6399 ≤ 11566253750907^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487825397 2500000000 11566253750907 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288874179/10000000000 : ℝ), (1097746597/2000000000 : ℝ), (-487825397/2500000000 : ℝ)] ![(10783646564907/25000000000000 : ℝ), (45299159979113/100000000000000 : ℝ), (11566253750907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288874179/10000000000 : ℝ)|^8447 ≤ (10783646564907/25000000000000 : ℝ)^6399
        have hw : |(5288874179/10000000000 : ℝ)|=(5288874179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097746597/2000000000 : ℝ)|^8447 ≤ (45299159979113/100000000000000 : ℝ)^6399
        have hw : |(1097746597/2000000000 : ℝ)|=(1097746597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487825397/2500000000 : ℝ)|^8447 ≤ (11566253750907/100000000000000 : ℝ)^6399
        have hw : |(-487825397/2500000000 : ℝ)|=(487825397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s2_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2170382207/5000000000 : ℝ)*x 0 + (1166859109/2500000000 : ℝ)*x 1 + (504568123/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170382207/5000000000 : ℝ)^8447 ≤ (2077061223523/6250000000000 : ℝ)^6399 := by
    have hnat : (2170382207 : ℕ)^8447*6250000000000^6399 ≤ 2077061223523^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170382207 5000000000 2077061223523 6250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1166859109/2500000000 : ℝ)^8447 ≤ (18286768194043/50000000000000 : ℝ)^6399 := by
    have hnat : (1166859109 : ℕ)^8447*50000000000000^6399 ≤ 18286768194043^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166859109 2500000000 18286768194043 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504568123/1250000000 : ℝ)^8447 ≤ (30193484019569/100000000000000 : ℝ)^6399 := by
    have hnat : (504568123 : ℕ)^8447*100000000000000^6399 ≤ 30193484019569^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504568123 1250000000 30193484019569 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170382207/5000000000 : ℝ), (1166859109/2500000000 : ℝ), (504568123/1250000000 : ℝ)] ![(2077061223523/6250000000000 : ℝ), (18286768194043/50000000000000 : ℝ), (30193484019569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170382207/5000000000 : ℝ)|^8447 ≤ (2077061223523/6250000000000 : ℝ)^6399
        have hw : |(2170382207/5000000000 : ℝ)|=(2170382207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1166859109/2500000000 : ℝ)|^8447 ≤ (18286768194043/50000000000000 : ℝ)^6399
        have hw : |(1166859109/2500000000 : ℝ)|=(1166859109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504568123/1250000000 : ℝ)|^8447 ≤ (30193484019569/100000000000000 : ℝ)^6399
        have hw : |(504568123/1250000000 : ℝ)|=(504568123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4987/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3127/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2387/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (506/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4987/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3127/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4987/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3127/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4987/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3127/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4987/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3127/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4987/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3127/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4987/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3127/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3127/50000 : ℝ) ^ (4223/1024 : ℝ) ≤ (271185758159891/25000000000000000000 : ℝ) := by
    have hpowers : (3127/50000 : ℝ)^4223 ≤ (271185758159891/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3127 : ℕ)^4223*25000000000000000000^1024 ≤ 271185758159891^1024*50000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127 50000 271185758159891 25000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3127/50000 : ℝ)) (X := (271185758159891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4987/25000 : ℝ) ^ (4223/1024 : ℝ) ≤ (2592976291171173/2000000000000000000 : ℝ) := by
    have hpowers : (4987/25000 : ℝ)^4223 ≤ (2592976291171173/2000000000000000000 : ℝ)^1024 := by
      have hnat : (4987 : ℕ)^4223*2000000000000000000^1024 ≤ 2592976291171173^1024*25000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4987 25000 2592976291171173 2000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4987/25000 : ℝ)) (X := (2592976291171173/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500271185758159891/12500000000000000000 : ℝ) ≤ (10000052605623403/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (12500271185758159891/12500000000000000000 : ℝ)^1024 ≤ (10000052605623403/10000000000000000 : ℝ)^4223 := by
      have hnat : (12500271185758159891 : ℕ)^1024*10000000000000000^4223 ≤ 10000052605623403^4223*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500271185758159891 12500000000000000000 10000052605623403 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000052605623403/10000000000000000 : ℝ)) (X := (12500271185758159891/12500000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50065366778795599107/50000000000000000000 : ℝ) ≤ (2000633696070739/2000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50065366778795599107/50000000000000000000 : ℝ)^1024 ≤ (2000633696070739/2000000000000000 : ℝ)^4223 := by
      have hnat : (50065366778795599107 : ℕ)^1024*2000000000000000^4223 ≤ 2000633696070739^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065366778795599107 50000000000000000000 2000633696070739 2000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000633696070739/2000000000000000 : ℝ)) (X := (50065366778795599107/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1002592976291171173/1000000000000000000 : ℝ) ≤ (10006284355083987/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (1002592976291171173/1000000000000000000 : ℝ)^1024 ≤ (10006284355083987/10000000000000000 : ℝ)^4223 := by
      have hnat : (1002592976291171173 : ℕ)^1024*10000000000000000^4223 ≤ 10006284355083987^4223*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1002592976291171173 1000000000000000000 10006284355083987 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006284355083987/10000000000000000 : ℝ)) (X := (1002592976291171173/1000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(271185758159891/25000000000000000000 : ℝ) ≤ ((68450873510140194173/68470000000000000000 : ℝ)+2*(778968682573/342350000000000 : ℝ)*(3127/50000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (68450873510140194173/68470000000000000000 : ℝ)+2*(778968682573/342350000000000 : ℝ)*(3127/50000 : ℝ)=(10000052605623403/10000000000000000 : ℝ) by norm_num, show 1+2*(271185758159891/25000000000000000000 : ℝ)=(12500271185758159891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2592976291171173/2000000000000000000 : ℝ)+(271185758159891/25000000000000000000 : ℝ) ≤ ((68450873510140194173/68470000000000000000 : ℝ)+(778968682573/342350000000000 : ℝ)*((4987/25000 : ℝ)+(3127/50000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (68450873510140194173/68470000000000000000 : ℝ)+(778968682573/342350000000000 : ℝ)*((4987/25000 : ℝ)+(3127/50000 : ℝ))=(2000633696070739/2000000000000000 : ℝ) by norm_num, show 1+(2592976291171173/2000000000000000000 : ℝ)+(271185758159891/25000000000000000000 : ℝ)=(50065366778795599107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2592976291171173/2000000000000000000 : ℝ) ≤ ((68450873510140194173/68470000000000000000 : ℝ)+2*(778968682573/342350000000000 : ℝ)*(4987/25000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (68450873510140194173/68470000000000000000 : ℝ)+2*(778968682573/342350000000000 : ℝ)*(4987/25000 : ℝ)=(10006284355083987/10000000000000000 : ℝ) by norm_num, show 1+2*(2592976291171173/2000000000000000000 : ℝ)=(1002592976291171173/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68450873510140194173/68470000000000000000 : ℝ)*(X 1 0+X 2 0)+(778968682573/342350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (3127/50000 : ℝ)) (hi := (4987/25000 : ℝ)) (c := (68450873510140194173/68470000000000000000 : ℝ)) (alpha := (778968682573/342350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68450873510140194173/68470000000000000000 : ℝ)*(X 0 1+X 2 1)+(778968682573/342350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (3127/50000 : ℝ)) (hi := (4987/25000 : ℝ)) (c := (68450873510140194173/68470000000000000000 : ℝ)) (alpha := (778968682573/342350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68450873510140194173/68470000000000000000 : ℝ)*(X 0 2+X 1 2)+(778968682573/342350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (3127/50000 : ℝ)) (hi := (4987/25000 : ℝ)) (c := (68450873510140194173/68470000000000000000 : ℝ)) (alpha := (778968682573/342350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050423393/5000000000 : ℝ)*X 0 0+(219630213/400000000 : ℝ)*X 0 1+(5176445543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((536920003/1000000000 : ℝ)*X 1 0+(-2263589359/10000000000 : ℝ)*X 1 1+(2588222829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369199927/10000000000 : ℝ)*X 2 0+(2588222859/5000000000 : ℝ)*X 2 1+(-2263589417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340610461/10000000000 : ℝ)*X 0 0+(2016216757/5000000000 : ℝ)*X 0 1+(1167877599/2500000000 : ℝ)*X 0 2+(4340610461/10000000000 : ℝ)*X 1 0+(2016216757/5000000000 : ℝ)*X 1 1+(1167877599/2500000000 : ℝ)*X 1 2+(4340610461/10000000000 : ℝ)*X 2 0+(2016216757/5000000000 : ℝ)*X 2 1+(1167877599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2100922741/10000000000 : ℝ)*X 0 0+(5178449389/10000000000 : ℝ)*X 0 1+(5488732839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057774807/2000000000 : ℝ)*X 1 0+(-975650963/5000000000 : ℝ)*X 1 1+(1372183221/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288874179/10000000000 : ℝ)*X 2 0+(1097746597/2000000000 : ℝ)*X 2 1+(-487825397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170382207/5000000000 : ℝ)*X 0 0+(1166859109/2500000000 : ℝ)*X 0 1+(504568123/1250000000 : ℝ)*X 0 2+(2170382207/5000000000 : ℝ)*X 1 0+(1166859109/2500000000 : ℝ)*X 1 1+(504568123/1250000000 : ℝ)*X 1 2+(2170382207/5000000000 : ℝ)*X 2 0+(1166859109/2500000000 : ℝ)*X 2 1+(504568123/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1059510235437240978881213217/213968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (860823853/100000000000000 : ℝ)*(base19) + (23508611/3125000000000 : ℝ)*(base23) + (12755663/50000000000000 : ℝ)*(lower2) + (147780357/100000000000000 : ℝ)*(upper3) + (54468579/100000000000000 : ℝ)*(upper5) + (148323830108393/6250000000000 : ℝ)*(major0) + (148323830108393/6250000000000 : ℝ)*(major1) + (148323830108393/6250000000000 : ℝ)*(major2) + (318158606093513/10000000000000 : ℝ)*(sp0) + (318159493573177/10000000000000 : ℝ)*(sp1) + (397699380535009/12500000000000 : ℝ)*(sp2) + (62590454184021/4000000000000 : ℝ)*(sp3) + (4867810247/50000000000000 : ℝ)*(sp4) + (327953473/6250000000000 : ℝ)*(sp7) + (782383300928047/50000000000000 : ℝ)*(f.failure) + (397699474569453/12500000000000 : ℝ)*(f.sum) + (146561957572443/34235000000000000000000000000 : ℝ)*base65 + (2574360095752581011/427937500000000000000000000000000 : ℝ)*base68 + (3592226965254956011/427937500000000000000000000000000 : ℝ)*base70 + (2596478628718893511/427937500000000000000000000000000 : ℝ)*base72 + (34028083943267/8558750000000000000000000000 : ℝ)*base73 + (6545900581145793989/427937500000000000000000000000000 : ℝ)*base75 + (1224511707248143511/427937500000000000000000000000000 : ℝ)*base78 + (1328478569299918989/427937500000000000000000000000000 : ℝ)*base79 + (19914741824717/8558750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8869793/1000000000000000000000 : ℝ)*base89 + (8869793/1000000000000000000000 : ℝ)*base91 + (8869793/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2191499803154056986767022069/342350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1678412767/100000000000000 : ℝ)*(base19) + (484622403/25000000000000 : ℝ)*(base23) + (20602337/50000000000000 : ℝ)*(upper2) + (58072349/25000000000000 : ℝ)*(upper3) + (61833281/50000000000000 : ℝ)*(upper5) + (480791765325549/20000000000000 : ℝ)*(major0) + (480791765325549/20000000000000 : ℝ)*(major1) + (480791765325549/20000000000000 : ℝ)*(major2) + (8636124879/50000000000000 : ℝ)*(sp1) + (23489185167/100000000000000 : ℝ)*(sp2) + (1611428770141659/50000000000000 : ℝ)*(sp4) + (1611419294810397/50000000000000 : ℝ)*(sp5) + (161141605630427/5000000000000 : ℝ)*(sp6) + (792529949797031/50000000000000 : ℝ)*(sp7) + (792529949797031/50000000000000 : ℝ)*(f.failure) + (1611428770141659/50000000000000 : ℝ)*(f.sum) + (1864336935593/855875000000000000000000000 : ℝ)*base65 + (10323302272793625977/1369400000000000000000000000000000 : ℝ)*base67 + (6408010916119225977/1369400000000000000000000000000000 : ℝ)*base69 + (267728967392025977/1369400000000000000000000000000000 : ℝ)*base71 + (6397474189763/1711750000000000000000000000 : ℝ)*base73 + (14709093437174025977/1369400000000000000000000000000000 : ℝ)*base75 + (7411895697925425977/1369400000000000000000000000000000 : ℝ)*base77 + (8756498771223974023/1369400000000000000000000000000000 : ℝ)*base80 + (30940833112949/6847000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1642711/1000000000000000000000 : ℝ)*base90 + (1642711/1000000000000000000000 : ℝ)*base92 + (1642711/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1254_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4987/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3127/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (506/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1254_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (506/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1254_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1254_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1254_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (506/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
