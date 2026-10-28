-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1045_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:50:29.033031+00:00
-- url     : https://prove2.me/submissions/165d7e95-d4a0-447b-bc01-7f54decdf794

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
theorem support_rectangle_w1045_s3_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209113731/10000000000 : ℝ)*x 0 + (340001959/625000000 : ℝ)*x 1 + (1044408659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209113731/10000000000 : ℝ)^4119 ≤ (6702218014577/50000000000000 : ℝ)^3095 := by
    have hnat : (2209113731 : ℕ)^4119*50000000000000^3095 ≤ 6702218014577^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209113731 10000000000 6702218014577 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340001959/625000000 : ℝ)^4119 ≤ (44475770582433/100000000000000 : ℝ)^3095 := by
    have hnat : (340001959 : ℕ)^4119*100000000000000^3095 ≤ 44475770582433^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340001959 625000000 44475770582433 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044408659/2000000000 : ℝ)^4119 ≤ (42119793382329/100000000000000 : ℝ)^3095 := by
    have hnat : (1044408659 : ℕ)^4119*100000000000000^3095 ≤ 42119793382329^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044408659 2000000000 42119793382329 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209113731/10000000000 : ℝ), (340001959/625000000 : ℝ), (1044408659/2000000000 : ℝ)] ![(6702218014577/50000000000000 : ℝ), (44475770582433/100000000000000 : ℝ), (42119793382329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209113731/10000000000 : ℝ)|^4119 ≤ (6702218014577/50000000000000 : ℝ)^3095
        have hw : |(-2209113731/10000000000 : ℝ)|=(2209113731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340001959/625000000 : ℝ)|^4119 ≤ (44475770582433/100000000000000 : ℝ)^3095
        have hw : |(340001959/625000000 : ℝ)|=(340001959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044408659/2000000000 : ℝ)|^4119 ≤ (42119793382329/100000000000000 : ℝ)^3095
        have hw : |(1044408659/2000000000 : ℝ)|=(1044408659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s3_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356239583/10000000000 : ℝ)*x 0 + (-2320800779/10000000000 : ℝ)*x 1 + (2611021733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356239583/10000000000 : ℝ)^4119 ≤ (5445799534359/12500000000000 : ℝ)^3095 := by
    have hnat : (5356239583 : ℕ)^4119*12500000000000^3095 ≤ 5445799534359^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356239583 10000000000 5445799534359 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320800779/10000000000 : ℝ)^4119 ≤ (14313808496591/100000000000000 : ℝ)^3095 := by
    have hnat : (2320800779 : ℕ)^4119*100000000000000^3095 ≤ 14313808496591^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320800779 10000000000 14313808496591 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611021733/5000000000 : ℝ)^4119 ≤ (10529948804477/25000000000000 : ℝ)^3095 := by
    have hnat : (2611021733 : ℕ)^4119*25000000000000^3095 ≤ 10529948804477^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611021733 5000000000 10529948804477 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356239583/10000000000 : ℝ), (-2320800779/10000000000 : ℝ), (2611021733/5000000000 : ℝ)] ![(5445799534359/12500000000000 : ℝ), (14313808496591/100000000000000 : ℝ), (10529948804477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356239583/10000000000 : ℝ)|^4119 ≤ (5445799534359/12500000000000 : ℝ)^3095
        have hw : |(5356239583/10000000000 : ℝ)|=(5356239583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2320800779/10000000000 : ℝ)|^4119 ≤ (14313808496591/100000000000000 : ℝ)^3095
        have hw : |(-2320800779/10000000000 : ℝ)|=(2320800779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611021733/5000000000 : ℝ)|^4119 ≤ (10529948804477/25000000000000 : ℝ)^3095
        have hw : |(2611021733/5000000000 : ℝ)|=(2611021733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s3_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356239623/10000000000 : ℝ)*x 0 + (5222043647/10000000000 : ℝ)*x 1 + (-2320800489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356239623/10000000000 : ℝ)^4119 ≤ (43566396707867/100000000000000 : ℝ)^3095 := by
    have hnat : (5356239623 : ℕ)^4119*100000000000000^3095 ≤ 43566396707867^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356239623 10000000000 43566396707867 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5222043647/10000000000 : ℝ)^4119 ≤ (4211979716083/10000000000000 : ℝ)^3095 := by
    have hnat : (5222043647 : ℕ)^4119*10000000000000^3095 ≤ 4211979716083^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222043647 10000000000 4211979716083 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320800489/10000000000 : ℝ)^4119 ≤ (1431380611621/10000000000000 : ℝ)^3095 := by
    have hnat : (2320800489 : ℕ)^4119*10000000000000^3095 ≤ 1431380611621^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320800489 10000000000 1431380611621 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356239623/10000000000 : ℝ), (5222043647/10000000000 : ℝ), (-2320800489/10000000000 : ℝ)] ![(43566396707867/100000000000000 : ℝ), (4211979716083/10000000000000 : ℝ), (1431380611621/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356239623/10000000000 : ℝ)|^4119 ≤ (43566396707867/100000000000000 : ℝ)^3095
        have hw : |(5356239623/10000000000 : ℝ)|=(5356239623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5222043647/10000000000 : ℝ)|^4119 ≤ (4211979716083/10000000000000 : ℝ)^3095
        have hw : |(5222043647/10000000000 : ℝ)|=(5222043647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2320800489/10000000000 : ℝ)|^4119 ≤ (1431380611621/10000000000000 : ℝ)^3095
        have hw : |(-2320800489/10000000000 : ℝ)|=(2320800489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s3_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375546877/10000000000 : ℝ)*x 0 + (833616101/2000000000 : ℝ)*x 1 + (918705047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375546877/10000000000 : ℝ)^4119 ≤ (332863103681/1000000000000 : ℝ)^3095 := by
    have hnat : (4375546877 : ℕ)^4119*1000000000000^3095 ≤ 332863103681^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375546877 10000000000 332863103681 1000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833616101/2000000000 : ℝ)^4119 ≤ (31202514447991/100000000000000 : ℝ)^3095 := by
    have hnat : (833616101 : ℕ)^4119*100000000000000^3095 ≤ 31202514447991^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833616101 2000000000 31202514447991 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (918705047/2000000000 : ℝ)^4119 ≤ (8877793791077/25000000000000 : ℝ)^3095 := by
    have hnat : (918705047 : ℕ)^4119*25000000000000^3095 ≤ 8877793791077^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918705047 2000000000 8877793791077 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375546877/10000000000 : ℝ), (833616101/2000000000 : ℝ), (918705047/2000000000 : ℝ)] ![(332863103681/1000000000000 : ℝ), (31202514447991/100000000000000 : ℝ), (8877793791077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375546877/10000000000 : ℝ)|^4119 ≤ (332863103681/1000000000000 : ℝ)^3095
        have hw : |(4375546877/10000000000 : ℝ)|=(4375546877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833616101/2000000000 : ℝ)|^4119 ≤ (31202514447991/100000000000000 : ℝ)^3095
        have hw : |(833616101/2000000000 : ℝ)|=(833616101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(918705047/2000000000 : ℝ)|^4119 ≤ (8877793791077/25000000000000 : ℝ)^3095
        have hw : |(918705047/2000000000 : ℝ)|=(918705047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s3_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157361/9765625 : ℝ)*x 0 + (652868907/1250000000 : ℝ)*x 1 + (5439117771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157361/9765625 : ℝ)^4119 ≤ (2680925859393/20000000000000 : ℝ)^3095 := by
    have hnat : (2157361 : ℕ)^4119*20000000000000^3095 ≤ 2680925859393^3095*9765625^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157361 9765625 2680925859393 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652868907/1250000000 : ℝ)^4119 ≤ (10532385014911/25000000000000 : ℝ)^3095 := by
    have hnat : (652868907 : ℕ)^4119*25000000000000^3095 ≤ 10532385014911^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652868907 1250000000 10532385014911 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439117771/10000000000 : ℝ)^4119 ≤ (44465830627669/100000000000000 : ℝ)^3095 := by
    have hnat : (5439117771 : ℕ)^4119*100000000000000^3095 ≤ 44465830627669^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439117771 10000000000 44465830627669 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157361/9765625 : ℝ), (652868907/1250000000 : ℝ), (5439117771/10000000000 : ℝ)] ![(2680925859393/20000000000000 : ℝ), (10532385014911/25000000000000 : ℝ), (44465830627669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157361/9765625 : ℝ)|^4119 ≤ (2680925859393/20000000000000 : ℝ)^3095
        have hw : |(-2157361/9765625 : ℝ)|=(2157361/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652868907/1250000000 : ℝ)|^4119 ≤ (10532385014911/25000000000000 : ℝ)^3095
        have hw : |(652868907/1250000000 : ℝ)|=(652868907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439117771/10000000000 : ℝ)|^4119 ≤ (44465830627669/100000000000000 : ℝ)^3095
        have hw : |(5439117771/10000000000 : ℝ)|=(5439117771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s3_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301419591/10000000000 : ℝ)*x 0 + (-1051862977/5000000000 : ℝ)*x 1 + (5439118123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301419591/10000000000 : ℝ)^4119 ≤ (10743495974359/25000000000000 : ℝ)^3095 := by
    have hnat : (5301419591 : ℕ)^4119*25000000000000^3095 ≤ 10743495974359^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301419591 10000000000 10743495974359 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051862977/5000000000 : ℝ)^4119 ≤ (628009081021/5000000000000 : ℝ)^3095 := by
    have hnat : (1051862977 : ℕ)^4119*5000000000000^3095 ≤ 628009081021^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051862977 5000000000 628009081021 5000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439118123/10000000000 : ℝ)^4119 ≤ (44465834457431/100000000000000 : ℝ)^3095 := by
    have hnat : (5439118123 : ℕ)^4119*100000000000000^3095 ≤ 44465834457431^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439118123 10000000000 44465834457431 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301419591/10000000000 : ℝ), (-1051862977/5000000000 : ℝ), (5439118123/10000000000 : ℝ)] ![(10743495974359/25000000000000 : ℝ), (628009081021/5000000000000 : ℝ), (44465834457431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301419591/10000000000 : ℝ)|^4119 ≤ (10743495974359/25000000000000 : ℝ)^3095
        have hw : |(5301419591/10000000000 : ℝ)|=(5301419591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051862977/5000000000 : ℝ)|^4119 ≤ (628009081021/5000000000000 : ℝ)^3095
        have hw : |(-1051862977/5000000000 : ℝ)|=(1051862977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439118123/10000000000 : ℝ)|^4119 ≤ (44465834457431/100000000000000 : ℝ)^3095
        have hw : |(5439118123/10000000000 : ℝ)|=(5439118123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s3_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325354843/2500000000 : ℝ)*x 0 + (5439118023/10000000000 : ℝ)*x 1 + (-210372639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325354843/2500000000 : ℝ)^4119 ≤ (8594796306969/20000000000000 : ℝ)^3095 := by
    have hnat : (1325354843 : ℕ)^4119*20000000000000^3095 ≤ 8594796306969^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325354843 2500000000 8594796306969 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439118023/10000000000 : ℝ)^4119 ≤ (4446583336943/10000000000000 : ℝ)^3095 := by
    have hnat : (5439118023 : ℕ)^4119*10000000000000^3095 ≤ 4446583336943^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439118023 10000000000 4446583336943 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210372639/1000000000 : ℝ)^4119 ≤ (12560185084791/100000000000000 : ℝ)^3095 := by
    have hnat : (210372639 : ℕ)^4119*100000000000000^3095 ≤ 12560185084791^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210372639 1000000000 12560185084791 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325354843/2500000000 : ℝ), (5439118023/10000000000 : ℝ), (-210372639/1000000000 : ℝ)] ![(8594796306969/20000000000000 : ℝ), (4446583336943/10000000000000 : ℝ), (12560185084791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325354843/2500000000 : ℝ)|^4119 ≤ (8594796306969/20000000000000 : ℝ)^3095
        have hw : |(1325354843/2500000000 : ℝ)|=(1325354843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439118023/10000000000 : ℝ)|^4119 ≤ (4446583336943/10000000000000 : ℝ)^3095
        have hw : |(5439118023/10000000000 : ℝ)|=(5439118023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210372639/1000000000 : ℝ)|^4119 ≤ (12560185084791/100000000000000 : ℝ)^3095
        have hw : |(-210372639/1000000000 : ℝ)|=(210372639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s3_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093898219/2500000000 : ℝ)*x 0 + (1147938583/2500000000 : ℝ)*x 1 + (4169862293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093898219/2500000000 : ℝ)^4119 ≤ (33286776075997/100000000000000 : ℝ)^3095 := by
    have hnat : (1093898219 : ℕ)^4119*100000000000000^3095 ≤ 33286776075997^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093898219 2500000000 33286776075997 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147938583/2500000000 : ℝ)^4119 ≤ (35492956474173/100000000000000 : ℝ)^3095 := by
    have hnat : (1147938583 : ℕ)^4119*100000000000000^3095 ≤ 35492956474173^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147938583 2500000000 35492956474173 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169862293/10000000000 : ℝ)^4119 ≤ (15610133716187/50000000000000 : ℝ)^3095 := by
    have hnat : (4169862293 : ℕ)^4119*50000000000000^3095 ≤ 15610133716187^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169862293 10000000000 15610133716187 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093898219/2500000000 : ℝ), (1147938583/2500000000 : ℝ), (4169862293/10000000000 : ℝ)] ![(33286776075997/100000000000000 : ℝ), (35492956474173/100000000000000 : ℝ), (15610133716187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093898219/2500000000 : ℝ)|^4119 ≤ (33286776075997/100000000000000 : ℝ)^3095
        have hw : |(1093898219/2500000000 : ℝ)|=(1093898219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147938583/2500000000 : ℝ)|^4119 ≤ (35492956474173/100000000000000 : ℝ)^3095
        have hw : |(1147938583/2500000000 : ℝ)|=(1147938583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169862293/10000000000 : ℝ)|^4119 ≤ (15610133716187/50000000000000 : ℝ)^3095
        have hw : |(4169862293/10000000000 : ℝ)|=(4169862293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (413/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14937/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16811/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (269/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16811/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (269/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16811/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (269/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16811/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (269/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16811/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (269/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16811/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (269/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (269/3125 : ℝ) ^ (8237/2048 : ℝ) ≤ (130060678532147/2500000000000000000 : ℝ) := by
    have hpowers : (269/3125 : ℝ)^8237 ≤ (130060678532147/2500000000000000000 : ℝ)^2048 := by
      have hnat : (269 : ℕ)^8237*2500000000000000000^2048 ≤ 130060678532147^2048*3125^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        269 3125 130060678532147 2500000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (269/3125 : ℝ)) (X := (130060678532147/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16811/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (19199876470878009/25000000000000000000 : ℝ) := by
    have hpowers : (16811/100000 : ℝ)^8237 ≤ (19199876470878009/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16811 : ℕ)^8237*25000000000000000000^2048 ≤ 19199876470878009^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16811 100000 19199876470878009 25000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16811/100000 : ℝ)) (X := (19199876470878009/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250130060678532147/1250000000000000000 : ℝ) ≤ (10000258690162229/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (1250130060678532147/1250000000000000000 : ℝ)^2048 ≤ (10000258690162229/10000000000000000 : ℝ)^8237 := by
      have hnat : (1250130060678532147 : ℕ)^2048*10000000000000000^8237 ≤ 10000258690162229^8237*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250130060678532147 1250000000000000000 10000258690162229 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000258690162229/10000000000000000 : ℝ)) (X := (1250130060678532147/1250000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25020500483256199479/25000000000000000000 : ℝ) ≤ (10002038220793849/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (25020500483256199479/25000000000000000000 : ℝ)^2048 ≤ (10002038220793849/10000000000000000 : ℝ)^8237 := by
      have hnat : (25020500483256199479 : ℕ)^2048*10000000000000000^8237 ≤ 10002038220793849^8237*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020500483256199479 25000000000000000000 10002038220793849 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002038220793849/10000000000000000 : ℝ)) (X := (25020500483256199479/25000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12519199876470878009/12500000000000000000 : ℝ) ≤ (10003817751425469/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (12519199876470878009/12500000000000000000 : ℝ)^2048 ≤ (10003817751425469/10000000000000000 : ℝ)^8237 := by
      have hnat : (12519199876470878009 : ℕ)^2048*10000000000000000^8237 ≤ 10003817751425469^8237*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12519199876470878009 12500000000000000000 10003817751425469 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003817751425469/10000000000000000 : ℝ)) (X := (12519199876470878009/12500000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(130060678532147/2500000000000000000 : ℝ) ≤ ((82001485636046794567/82030000000000000000 : ℝ)+2*(88976531581/41015000000000 : ℝ)*(269/3125 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (82001485636046794567/82030000000000000000 : ℝ)+2*(88976531581/41015000000000 : ℝ)*(269/3125 : ℝ)=(10000258690162229/10000000000000000 : ℝ) by norm_num, show 1+2*(130060678532147/2500000000000000000 : ℝ)=(1250130060678532147/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19199876470878009/25000000000000000000 : ℝ)+(130060678532147/2500000000000000000 : ℝ) ≤ ((82001485636046794567/82030000000000000000 : ℝ)+(88976531581/41015000000000 : ℝ)*((16811/100000 : ℝ)+(269/3125 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (82001485636046794567/82030000000000000000 : ℝ)+(88976531581/41015000000000 : ℝ)*((16811/100000 : ℝ)+(269/3125 : ℝ))=(10002038220793849/10000000000000000 : ℝ) by norm_num, show 1+(19199876470878009/25000000000000000000 : ℝ)+(130060678532147/2500000000000000000 : ℝ)=(25020500483256199479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19199876470878009/25000000000000000000 : ℝ) ≤ ((82001485636046794567/82030000000000000000 : ℝ)+2*(88976531581/41015000000000 : ℝ)*(16811/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (82001485636046794567/82030000000000000000 : ℝ)+2*(88976531581/41015000000000 : ℝ)*(16811/100000 : ℝ)=(10003817751425469/10000000000000000 : ℝ) by norm_num, show 1+2*(19199876470878009/25000000000000000000 : ℝ)=(12519199876470878009/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (82001485636046794567/82030000000000000000 : ℝ)*(X 1 0+X 2 0)+(88976531581/41015000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (269/3125 : ℝ)) (hi := (16811/100000 : ℝ)) (c := (82001485636046794567/82030000000000000000 : ℝ)) (alpha := (88976531581/41015000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (82001485636046794567/82030000000000000000 : ℝ)*(X 0 1+X 2 1)+(88976531581/41015000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (269/3125 : ℝ)) (hi := (16811/100000 : ℝ)) (c := (82001485636046794567/82030000000000000000 : ℝ)) (alpha := (88976531581/41015000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (82001485636046794567/82030000000000000000 : ℝ)*(X 0 2+X 1 2)+(88976531581/41015000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (269/3125 : ℝ)) (hi := (16811/100000 : ℝ)) (c := (82001485636046794567/82030000000000000000 : ℝ)) (alpha := (88976531581/41015000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209113731/10000000000 : ℝ)*X 0 0+(340001959/625000000 : ℝ)*X 0 1+(1044408659/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356239583/10000000000 : ℝ)*X 1 0+(-2320800779/10000000000 : ℝ)*X 1 1+(2611021733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356239623/10000000000 : ℝ)*X 2 0+(5222043647/10000000000 : ℝ)*X 2 1+(-2320800489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375546877/10000000000 : ℝ)*X 0 0+(833616101/2000000000 : ℝ)*X 0 1+(918705047/2000000000 : ℝ)*X 0 2+(4375546877/10000000000 : ℝ)*X 1 0+(833616101/2000000000 : ℝ)*X 1 1+(918705047/2000000000 : ℝ)*X 1 2+(4375546877/10000000000 : ℝ)*X 2 0+(833616101/2000000000 : ℝ)*X 2 1+(918705047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157361/9765625 : ℝ)*X 0 0+(652868907/1250000000 : ℝ)*X 0 1+(5439117771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301419591/10000000000 : ℝ)*X 1 0+(-1051862977/5000000000 : ℝ)*X 1 1+(5439118123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325354843/2500000000 : ℝ)*X 2 0+(5439118023/10000000000 : ℝ)*X 2 1+(-210372639/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093898219/2500000000 : ℝ)*X 0 0+(1147938583/2500000000 : ℝ)*X 0 1+(4169862293/10000000000 : ℝ)*X 0 2+(1093898219/2500000000 : ℝ)*X 1 0+(1147938583/2500000000 : ℝ)*X 1 1+(4169862293/10000000000 : ℝ)*X 1 2+(1093898219/2500000000 : ℝ)*X 2 0+(1147938583/2500000000 : ℝ)*X 2 1+(4169862293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3501857099524961442864853833/512687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (865167481/50000000000000 : ℝ)*(base19) + (1472293101/100000000000000 : ℝ)*(base23) + (156563299/100000000000000 : ℝ)*(lower2) + (113040033/100000000000000 : ℝ)*(upper3) + (84389897/50000000000000 : ℝ)*(upper5) + (1734496532856933/50000000000000 : ℝ)*(major0) + (1734496532856933/50000000000000 : ℝ)*(major1) + (867248266428467/25000000000000 : ℝ)*(major2) + (4587439233479247/100000000000000 : ℝ)*(sp0) + (143358562354231/3125000000000 : ℝ)*(sp1) + (4587474253377253/100000000000000 : ℝ)*(sp2) + (1175247806113583/50000000000000 : ℝ)*(sp3) + (18246095553/50000000000000 : ℝ)*(sp4) + (7282925217/50000000000000 : ℝ)*(sp7) + (2938137722597/125000000000 : ℝ)*(f.failure) + (4587475725670353/100000000000000 : ℝ)*(f.sum) + (9371135234433/8203000000000000000000000000 : ℝ)*base65 + (55422708684472316989/4101500000000000000000000000000000 : ℝ)*base68 + (10053665797600488789/2050750000000000000000000000000000 : ℝ)*base69 + (46556349628892316989/4101500000000000000000000000000000 : ℝ)*base72 + (36662515649629/4101500000000000000000000000 : ℝ)*base73 + (10912099327739738789/2050750000000000000000000000000000 : ℝ)*base75 + (6779689834113755153/315500000000000000000000000000000 : ℝ)*base78 + (8439906432785755153/315500000000000000000000000000000 : ℝ)*base80 + (44880134450219/8203000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (49771/6250000000000000000 : ℝ)*base89 + (49771/6250000000000000000 : ℝ)*base91 + (75229/6250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2998013705515139959506767469/512687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1527219017/100000000000000 : ℝ)*(base19) + (1327950123/100000000000000 : ℝ)*(base23) + (18258381/100000000000000 : ℝ)*(upper2) + (16420753/6250000000000 : ℝ)*(upper3) + (16387049/100000000000000 : ℝ)*(upper5) + (437270700790331/12500000000000 : ℝ)*(major0) + (437270700790331/12500000000000 : ℝ)*(major1) + (437270700790331/12500000000000 : ℝ)*(major2) + (5497201943/20000000000000 : ℝ)*(sp1) + (11682695391/50000000000000 : ℝ)*(sp2) + (578256774360187/12500000000000 : ℝ)*(sp4) + (1156506295413191/25000000000000 : ℝ)*(sp5) + (4626029501540591/100000000000000 : ℝ)*(sp6) + (1185138411421171/50000000000000 : ℝ)*(sp7) + (1185138411421171/50000000000000 : ℝ)*(f.failure) + (578256774360187/12500000000000 : ℝ)*(f.sum) + (2945445235201/1025375000000000000000000000 : ℝ)*base65 + (18347272732610129/78875000000000000000000000000000 : ℝ)*base67 + (136313424562360129/78875000000000000000000000000000 : ℝ)*base69 + (158995639323735129/78875000000000000000000000000000 : ℝ)*base71 + (14382514459243/8203000000000000000000000000 : ℝ)*base73 + (42026795278389871/78875000000000000000000000000000 : ℝ)*base76 + (264139999068639871/78875000000000000000000000000000 : ℝ)*base78 + (863471240944985129/78875000000000000000000000000000 : ℝ)*base79 + (25690250157199/4101500000000000000000000000 : ℝ)*base81 + (32106347/2500000000000000000000 : ℝ)*base90 + (32106347/2500000000000000000000 : ℝ)*base92 + (32106347/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1045_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1045_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1045_s4_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213004841/10000000000 : ℝ)*x 0 + (1081400911/2000000000 : ℝ)*x 1 + (2626264417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213004841/10000000000 : ℝ)^4119 ≤ (839741704691/6250000000000 : ℝ)^3095 := by
    have hnat : (2213004841 : ℕ)^4119*6250000000000^3095 ≤ 839741704691^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213004841 10000000000 839741704691 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081400911/2000000000 : ℝ)^4119 ≤ (5514597548621/12500000000000 : ℝ)^3095 := by
    have hnat : (1081400911 : ℕ)^4119*12500000000000^3095 ≤ 5514597548621^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081400911 2000000000 5514597548621 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626264417/5000000000 : ℝ)^4119 ≤ (42447352318379/100000000000000 : ℝ)^3095 := by
    have hnat : (2626264417 : ℕ)^4119*100000000000000^3095 ≤ 42447352318379^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626264417 5000000000 42447352318379 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213004841/10000000000 : ℝ), (1081400911/2000000000 : ℝ), (2626264417/5000000000 : ℝ)] ![(839741704691/6250000000000 : ℝ), (5514597548621/12500000000000 : ℝ), (42447352318379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213004841/10000000000 : ℝ)|^4119 ≤ (839741704691/6250000000000 : ℝ)^3095
        have hw : |(-2213004841/10000000000 : ℝ)|=(2213004841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081400911/2000000000 : ℝ)|^4119 ≤ (5514597548621/12500000000000 : ℝ)^3095
        have hw : |(1081400911/2000000000 : ℝ)|=(1081400911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626264417/5000000000 : ℝ)|^4119 ≤ (42447352318379/100000000000000 : ℝ)^3095
        have hw : |(2626264417/5000000000 : ℝ)|=(2626264417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s4_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668509599/1250000000 : ℝ)*x 0 + (-1145798007/5000000000 : ℝ)*x 1 + (1313132213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668509599/1250000000 : ℝ)^4119 ≤ (21739028694477/50000000000000 : ℝ)^3095 := by
    have hnat : (668509599 : ℕ)^4119*50000000000000^3095 ≤ 21739028694477^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668509599 1250000000 21739028694477 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145798007/5000000000 : ℝ)^4119 ≤ (2814918016001/20000000000000 : ℝ)^3095 := by
    have hnat : (1145798007 : ℕ)^4119*20000000000000^3095 ≤ 2814918016001^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145798007 5000000000 2814918016001 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313132213/2500000000 : ℝ)^4119 ≤ (4244735251197/10000000000000 : ℝ)^3095 := by
    have hnat : (1313132213 : ℕ)^4119*10000000000000^3095 ≤ 4244735251197^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313132213 2500000000 4244735251197 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668509599/1250000000 : ℝ), (-1145798007/5000000000 : ℝ), (1313132213/2500000000 : ℝ)] ![(21739028694477/50000000000000 : ℝ), (2814918016001/20000000000000 : ℝ), (4244735251197/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668509599/1250000000 : ℝ)|^4119 ≤ (21739028694477/50000000000000 : ℝ)^3095
        have hw : |(668509599/1250000000 : ℝ)|=(668509599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1145798007/5000000000 : ℝ)|^4119 ≤ (2814918016001/20000000000000 : ℝ)^3095
        have hw : |(-1145798007/5000000000 : ℝ)|=(1145798007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313132213/2500000000 : ℝ)|^4119 ≤ (4244735251197/10000000000000 : ℝ)^3095
        have hw : |(1313132213/2500000000 : ℝ)|=(1313132213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s4_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337019207/2500000000 : ℝ)*x 0 + (5252528791/10000000000 : ℝ)*x 1 + (-2291596047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337019207/2500000000 : ℝ)^4119 ≤ (10869514444613/25000000000000 : ℝ)^3095 := by
    have hnat : (1337019207 : ℕ)^4119*25000000000000^3095 ≤ 10869514444613^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337019207 2500000000 10869514444613 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252528791/10000000000 : ℝ)^4119 ≤ (42447351855911/100000000000000 : ℝ)^3095 := by
    have hnat : (5252528791 : ℕ)^4119*100000000000000^3095 ≤ 42447351855911^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252528791 10000000000 42447351855911 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291596047/10000000000 : ℝ)^4119 ≤ (14074590349743/100000000000000 : ℝ)^3095 := by
    have hnat : (2291596047 : ℕ)^4119*100000000000000^3095 ≤ 14074590349743^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291596047 10000000000 14074590349743 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337019207/2500000000 : ℝ), (5252528791/10000000000 : ℝ), (-2291596047/10000000000 : ℝ)] ![(10869514444613/25000000000000 : ℝ), (42447351855911/100000000000000 : ℝ), (14074590349743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337019207/2500000000 : ℝ)|^4119 ≤ (10869514444613/25000000000000 : ℝ)^3095
        have hw : |(1337019207/2500000000 : ℝ)|=(1337019207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252528791/10000000000 : ℝ)|^4119 ≤ (42447351855911/100000000000000 : ℝ)^3095
        have hw : |(5252528791/10000000000 : ℝ)|=(5252528791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2291596047/10000000000 : ℝ)|^4119 ≤ (14074590349743/100000000000000 : ℝ)^3095
        have hw : |(-2291596047/10000000000 : ℝ)|=(2291596047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s4_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218892877/500000000 : ℝ)*x 0 + (264359633/625000000 : ℝ)*x 1 + (4531243461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218892877/500000000 : ℝ)^4119 ≤ (33309706227353/100000000000000 : ℝ)^3095 := by
    have hnat : (218892877 : ℕ)^4119*100000000000000^3095 ≤ 33309706227353^3095*500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218892877 500000000 33309706227353 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264359633/625000000 : ℝ)^4119 ≤ (31818460073601/100000000000000 : ℝ)^3095 := by
    have hnat : (264359633 : ℕ)^4119*100000000000000^3095 ≤ 31818460073601^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264359633 625000000 31818460073601 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531243461/10000000000 : ℝ)^4119 ≤ (4358979211593/12500000000000 : ℝ)^3095 := by
    have hnat : (4531243461 : ℕ)^4119*12500000000000^3095 ≤ 4358979211593^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531243461 10000000000 4358979211593 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218892877/500000000 : ℝ), (264359633/625000000 : ℝ), (4531243461/10000000000 : ℝ)] ![(33309706227353/100000000000000 : ℝ), (31818460073601/100000000000000 : ℝ), (4358979211593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218892877/500000000 : ℝ)|^4119 ≤ (33309706227353/100000000000000 : ℝ)^3095
        have hw : |(218892877/500000000 : ℝ)|=(218892877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264359633/625000000 : ℝ)|^4119 ≤ (31818460073601/100000000000000 : ℝ)^3095
        have hw : |(264359633/625000000 : ℝ)|=(264359633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531243461/10000000000 : ℝ)|^4119 ≤ (4358979211593/12500000000000 : ℝ)^3095
        have hw : |(4531243461/10000000000 : ℝ)|=(4531243461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s4_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213013467/10000000000 : ℝ)*x 0 + (5252985269/10000000000 : ℝ)*x 1 + (1081309209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213013467/10000000000 : ℝ)^4119 ≤ (13435936973681/100000000000000 : ℝ)^3095 := by
    have hnat : (2213013467 : ℕ)^4119*100000000000000^3095 ≤ 13435936973681^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213013467 10000000000 13435936973681 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252985269/10000000000 : ℝ)^4119 ≤ (21226130689989/50000000000000 : ℝ)^3095 := by
    have hnat : (5252985269 : ℕ)^4119*50000000000000^3095 ≤ 21226130689989^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252985269 10000000000 21226130689989 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081309209/2000000000 : ℝ)^4119 ≤ (44111801631933/100000000000000 : ℝ)^3095 := by
    have hnat : (1081309209 : ℕ)^4119*100000000000000^3095 ≤ 44111801631933^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081309209 2000000000 44111801631933 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213013467/10000000000 : ℝ), (5252985269/10000000000 : ℝ), (1081309209/2000000000 : ℝ)] ![(13435936973681/100000000000000 : ℝ), (21226130689989/50000000000000 : ℝ), (44111801631933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213013467/10000000000 : ℝ)|^4119 ≤ (13435936973681/100000000000000 : ℝ)^3095
        have hw : |(-2213013467/10000000000 : ℝ)|=(2213013467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252985269/10000000000 : ℝ)|^4119 ≤ (21226130689989/50000000000000 : ℝ)^3095
        have hw : |(5252985269/10000000000 : ℝ)|=(5252985269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081309209/2000000000 : ℝ)|^4119 ≤ (44111801631933/100000000000000 : ℝ)^3095
        have hw : |(1081309209/2000000000 : ℝ)|=(1081309209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s4_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309234749/10000000000 : ℝ)*x 0 + (-2137578873/10000000000 : ℝ)*x 1 + (1081309199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309234749/10000000000 : ℝ)^4119 ≤ (43058315082283/100000000000000 : ℝ)^3095 := by
    have hnat : (5309234749 : ℕ)^4119*100000000000000^3095 ≤ 43058315082283^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309234749 10000000000 43058315082283 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2137578873/10000000000 : ℝ)^4119 ≤ (3207470953967/25000000000000 : ℝ)^3095 := by
    have hnat : (2137578873 : ℕ)^4119*25000000000000^3095 ≤ 3207470953967^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137578873 10000000000 3207470953967 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081309199/2000000000 : ℝ)^4119 ≤ (44111801089013/100000000000000 : ℝ)^3095 := by
    have hnat : (1081309199 : ℕ)^4119*100000000000000^3095 ≤ 44111801089013^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081309199 2000000000 44111801089013 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309234749/10000000000 : ℝ), (-2137578873/10000000000 : ℝ), (1081309199/2000000000 : ℝ)] ![(43058315082283/100000000000000 : ℝ), (3207470953967/25000000000000 : ℝ), (44111801089013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309234749/10000000000 : ℝ)|^4119 ≤ (43058315082283/100000000000000 : ℝ)^3095
        have hw : |(5309234749/10000000000 : ℝ)|=(5309234749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2137578873/10000000000 : ℝ)|^4119 ≤ (3207470953967/25000000000000 : ℝ)^3095
        have hw : |(-2137578873/10000000000 : ℝ)|=(2137578873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081309199/2000000000 : ℝ)|^4119 ≤ (44111801089013/100000000000000 : ℝ)^3095
        have hw : |(1081309199/2000000000 : ℝ)|=(1081309199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s4_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309234711/10000000000 : ℝ)*x 0 + (168954563/312500000 : ℝ)*x 1 + (-133598681/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309234711/10000000000 : ℝ)^4119 ≤ (5382289334017/12500000000000 : ℝ)^3095 := by
    have hnat : (5309234711 : ℕ)^4119*12500000000000^3095 ≤ 5382289334017^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309234711 10000000000 5382289334017 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168954563/312500000 : ℝ)^4119 ≤ (44111801317039/100000000000000 : ℝ)^3095 := by
    have hnat : (168954563 : ℕ)^4119*100000000000000^3095 ≤ 44111801317039^3095*312500000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168954563 312500000 44111801317039 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133598681/625000000 : ℝ)^4119 ≤ (12829883999589/100000000000000 : ℝ)^3095 := by
    have hnat : (133598681 : ℕ)^4119*100000000000000^3095 ≤ 12829883999589^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133598681 625000000 12829883999589 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309234711/10000000000 : ℝ), (168954563/312500000 : ℝ), (-133598681/625000000 : ℝ)] ![(5382289334017/12500000000000 : ℝ), (44111801317039/100000000000000 : ℝ), (12829883999589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309234711/10000000000 : ℝ)|^4119 ≤ (5382289334017/12500000000000 : ℝ)^3095
        have hw : |(5309234711/10000000000 : ℝ)|=(5309234711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168954563/312500000 : ℝ)|^4119 ≤ (44111801317039/100000000000000 : ℝ)^3095
        have hw : |(168954563/312500000 : ℝ)|=(168954563/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133598681/625000000 : ℝ)|^4119 ≤ (12829883999589/100000000000000 : ℝ)^3095
        have hw : |(-133598681/625000000 : ℝ)|=(133598681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s4_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188937023/5000000000 : ℝ)*x 0 + (4530351939/10000000000 : ℝ)*x 1 + (846129887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188937023/5000000000 : ℝ)^4119 ≤ (16654936684067/50000000000000 : ℝ)^3095 := by
    have hnat : (2188937023 : ℕ)^4119*50000000000000^3095 ≤ 16654936684067^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188937023 5000000000 16654936684067 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530351939/10000000000 : ℝ)^4119 ≤ (34862702942687/100000000000000 : ℝ)^3095 := by
    have hnat : (4530351939 : ℕ)^4119*100000000000000^3095 ≤ 34862702942687^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530351939 10000000000 34862702942687 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846129887/2000000000 : ℝ)^4119 ≤ (7956855917839/25000000000000 : ℝ)^3095 := by
    have hnat : (846129887 : ℕ)^4119*25000000000000^3095 ≤ 7956855917839^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846129887 2000000000 7956855917839 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188937023/5000000000 : ℝ), (4530351939/10000000000 : ℝ), (846129887/2000000000 : ℝ)] ![(16654936684067/50000000000000 : ℝ), (34862702942687/100000000000000 : ℝ), (7956855917839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188937023/5000000000 : ℝ)|^4119 ≤ (16654936684067/50000000000000 : ℝ)^3095
        have hw : |(2188937023/5000000000 : ℝ)|=(2188937023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530351939/10000000000 : ℝ)|^4119 ≤ (34862702942687/100000000000000 : ℝ)^3095
        have hw : |(4530351939/10000000000 : ℝ)|=(4530351939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846129887/2000000000 : ℝ)|^4119 ≤ (7956855917839/25000000000000 : ℝ)^3095
        have hw : |(846129887/2000000000 : ℝ)|=(846129887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (343/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14247/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (413/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (413/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (413/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (413/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (413/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (413/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (413/4000 : ℝ) ^ (8237/2048 : ℝ) ≤ (2702917531997371/25000000000000000000 : ℝ) := by
    have hpowers : (413/4000 : ℝ)^8237 ≤ (2702917531997371/25000000000000000000 : ℝ)^2048 := by
      have hnat : (413 : ℕ)^8237*25000000000000000000^2048 ≤ 2702917531997371^2048*4000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 4000 2702917531997371 25000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/4000 : ℝ)) (X := (2702917531997371/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14937/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (2387151055637163/5000000000000000000 : ℝ) := by
    have hpowers : (14937/100000 : ℝ)^8237 ≤ (2387151055637163/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14937 : ℕ)^8237*5000000000000000000^2048 ≤ 2387151055637163^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14937 100000 2387151055637163 5000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14937/100000 : ℝ)) (X := (2387151055637163/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502702917531997371/12500000000000000000 : ℝ) ≤ (10000537586546441/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (12502702917531997371/12500000000000000000 : ℝ)^2048 ≤ (10000537586546441/10000000000000000 : ℝ)^8237 := by
      have hnat : (12502702917531997371 : ℕ)^2048*10000000000000000^8237 ≤ 10000537586546441^8237*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502702917531997371 12500000000000000000 10000537586546441 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537586546441/10000000000000000 : ℝ)) (X := (12502702917531997371/12500000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507319336405091593/12500000000000000000 : ℝ) ≤ (125018194372447/125000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (12507319336405091593/12500000000000000000 : ℝ)^2048 ≤ (125018194372447/125000000000000 : ℝ)^8237 := by
      have hnat : (12507319336405091593 : ℕ)^2048*125000000000000^8237 ≤ 125018194372447^8237*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507319336405091593 12500000000000000000 125018194372447 125000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125018194372447/125000000000000 : ℝ)) (X := (12507319336405091593/12500000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502387151055637163/2500000000000000000 : ℝ) ≤ (10002373513045079/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (2502387151055637163/2500000000000000000 : ℝ)^2048 ≤ (10002373513045079/10000000000000000 : ℝ)^8237 := by
      have hnat : (2502387151055637163 : ℕ)^2048*10000000000000000^8237 ≤ 10002373513045079^8237*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502387151055637163 2500000000000000000 10002373513045079 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002373513045079/10000000000000000 : ℝ)) (X := (2502387151055637163/2500000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2702917531997371/25000000000000000000 : ℝ) ≤ ((23051761704026874271/23060000000000000000 : ℝ)+2*(917963249319/461200000000000 : ℝ)*(413/4000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (23051761704026874271/23060000000000000000 : ℝ)+2*(917963249319/461200000000000 : ℝ)*(413/4000 : ℝ)=(10000537586546441/10000000000000000 : ℝ) by norm_num, show 1+2*(2702917531997371/25000000000000000000 : ℝ)=(12502702917531997371/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2387151055637163/5000000000000000000 : ℝ)+(2702917531997371/25000000000000000000 : ℝ) ≤ ((23051761704026874271/23060000000000000000 : ℝ)+(917963249319/461200000000000 : ℝ)*((14937/100000 : ℝ)+(413/4000 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (23051761704026874271/23060000000000000000 : ℝ)+(917963249319/461200000000000 : ℝ)*((14937/100000 : ℝ)+(413/4000 : ℝ))=(125018194372447/125000000000000 : ℝ) by norm_num, show 1+(2387151055637163/5000000000000000000 : ℝ)+(2702917531997371/25000000000000000000 : ℝ)=(12507319336405091593/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2387151055637163/5000000000000000000 : ℝ) ≤ ((23051761704026874271/23060000000000000000 : ℝ)+2*(917963249319/461200000000000 : ℝ)*(14937/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (23051761704026874271/23060000000000000000 : ℝ)+2*(917963249319/461200000000000 : ℝ)*(14937/100000 : ℝ)=(10002373513045079/10000000000000000 : ℝ) by norm_num, show 1+2*(2387151055637163/5000000000000000000 : ℝ)=(2502387151055637163/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23051761704026874271/23060000000000000000 : ℝ)*(X 1 0+X 2 0)+(917963249319/461200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (23051761704026874271/23060000000000000000 : ℝ)) (alpha := (917963249319/461200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23051761704026874271/23060000000000000000 : ℝ)*(X 0 1+X 2 1)+(917963249319/461200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (23051761704026874271/23060000000000000000 : ℝ)) (alpha := (917963249319/461200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23051761704026874271/23060000000000000000 : ℝ)*(X 0 2+X 1 2)+(917963249319/461200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (23051761704026874271/23060000000000000000 : ℝ)) (alpha := (917963249319/461200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2213004841/10000000000 : ℝ)*X 0 0+(1081400911/2000000000 : ℝ)*X 0 1+(2626264417/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668509599/1250000000 : ℝ)*X 1 0+(-1145798007/5000000000 : ℝ)*X 1 1+(1313132213/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337019207/2500000000 : ℝ)*X 2 0+(5252528791/10000000000 : ℝ)*X 2 1+(-2291596047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218892877/500000000 : ℝ)*X 0 0+(264359633/625000000 : ℝ)*X 0 1+(4531243461/10000000000 : ℝ)*X 0 2+(218892877/500000000 : ℝ)*X 1 0+(264359633/625000000 : ℝ)*X 1 1+(4531243461/10000000000 : ℝ)*X 1 2+(218892877/500000000 : ℝ)*X 2 0+(264359633/625000000 : ℝ)*X 2 1+(4531243461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2213013467/10000000000 : ℝ)*X 0 0+(5252985269/10000000000 : ℝ)*X 0 1+(1081309209/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309234749/10000000000 : ℝ)*X 1 0+(-2137578873/10000000000 : ℝ)*X 1 1+(1081309199/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309234711/10000000000 : ℝ)*X 2 0+(168954563/312500000 : ℝ)*X 2 1+(-133598681/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188937023/5000000000 : ℝ)*X 0 0+(4530351939/10000000000 : ℝ)*X 0 1+(846129887/2000000000 : ℝ)*X 0 2+(2188937023/5000000000 : ℝ)*X 1 0+(4530351939/10000000000 : ℝ)*X 1 1+(846129887/2000000000 : ℝ)*X 1 2+(2188937023/5000000000 : ℝ)*X 2 0+(4530351939/10000000000 : ℝ)*X 2 1+(846129887/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2456969298439388589688339977/288250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1802223301/100000000000000 : ℝ)*(base19) + (27309209/1562500000000 : ℝ)*(base23) + (52416607/100000000000000 : ℝ)*(lower2) + (247641891/100000000000000 : ℝ)*(upper3) + (858889/625000000000 : ℝ)*(upper5) + (4895251350507561/100000000000000 : ℝ)*(major0) + (4895251350507561/100000000000000 : ℝ)*(major1) + (2447625675253781/50000000000000 : ℝ)*(major2) + (258942083625041/4000000000000 : ℝ)*(sp0) + (6473590518379937/100000000000000 : ℝ)*(sp1) + (3236795286406931/50000000000000 : ℝ)*(sp2) + (6633774362351/200000000000 : ℝ)*(sp3) + (20114988607/50000000000000 : ℝ)*(sp4) + (5728777891/25000000000000 : ℝ)*(sp7) + (414613762035883/12500000000000 : ℝ)*(f.failure) + (3236796160301619/50000000000000 : ℝ)*(f.sum) + (13310266127517/46120000000000000000000000000 : ℝ)*base65 + (508474111373763031/2306000000000000000000000000000000 : ℝ)*base67 + (12514800188168343651/1153000000000000000000000000000000 : ℝ)*base69 + (15208603772007763031/2306000000000000000000000000000000 : ℝ)*base71 + (161106603394123/46120000000000000000000000000 : ℝ)*base74 + (34219657561036343651/1153000000000000000000000000000000 : ℝ)*base75 + (11447122450149813031/2306000000000000000000000000000000 : ℝ)*base77 + (35710486048201813031/2306000000000000000000000000000000 : ℝ)*base79 + (102970708003399/23060000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (393869/625000000000000000000 : ℝ)*base89 + (393869/625000000000000000000 : ℝ)*base91 + (5856131/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2795691694966890847181413743/576500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1243104381/100000000000000 : ℝ)*(base19) + (1294634681/100000000000000 : ℝ)*(base23) + (84631661/100000000000000 : ℝ)*(upper2) + (1461879/10000000000000 : ℝ)*(upper3) + (342254177/100000000000000 : ℝ)*(upper5) + (2462181413124389/50000000000000 : ℝ)*(major0) + (2462181413124389/50000000000000 : ℝ)*(major1) + (2462181413124389/50000000000000 : ℝ)*(major2) + (34011476217/100000000000000 : ℝ)*(sp1) + (25637234317/100000000000000 : ℝ)*(sp2) + (1628022531488189/25000000000000 : ℝ)*(sp4) + (3256027435686079/50000000000000 : ℝ)*(sp5) + (6512063194083757/100000000000000 : ℝ)*(sp6) + (3336635364897397/100000000000000 : ℝ)*(sp7) + (3336635364897397/100000000000000 : ℝ)*(f.failure) + (1628022531488189/25000000000000 : ℝ)*(f.sum) + (71691170170209/11530000000000000000000000000 : ℝ)*base66 + (11416969619350245419/1153000000000000000000000000000000 : ℝ)*base67 + (6988854016446245419/1153000000000000000000000000000000 : ℝ)*base69 + (6237584762754581/1153000000000000000000000000000000 : ℝ)*base72 + (44816106140261/11530000000000000000000000000 : ℝ)*base73 + (12655768221124245419/1153000000000000000000000000000000 : ℝ)*base75 + (3346964570803754581/1153000000000000000000000000000000 : ℝ)*base78 + (10291144105615245419/1153000000000000000000000000000000 : ℝ)*base79 + (14456138490629/11530000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (20768829/5000000000000000000000 : ℝ)*base90 + (20768829/5000000000000000000000 : ℝ)*base92 + (20768829/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1045_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1045_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1045_s5_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11069487/50000000 : ℝ)*x 0 + (1349402911/2500000000 : ℝ)*x 1 + (5261336483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11069487/50000000 : ℝ)^4119 ≤ (6721539842357/50000000000000 : ℝ)^3095 := by
    have hnat : (11069487 : ℕ)^4119*50000000000000^3095 ≤ 6721539842357^3095*50000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11069487 50000000 6721539842357 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349402911/2500000000 : ℝ)^4119 ≤ (4401481481973/10000000000000 : ℝ)^3095 := by
    have hnat : (1349402911 : ℕ)^4119*10000000000000^3095 ≤ 4401481481973^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349402911 2500000000 4401481481973 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261336483/10000000000 : ℝ)^4119 ≤ (42542105479661/100000000000000 : ℝ)^3095 := by
    have hnat : (5261336483 : ℕ)^4119*100000000000000^3095 ≤ 42542105479661^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261336483 10000000000 42542105479661 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11069487/50000000 : ℝ), (1349402911/2500000000 : ℝ), (5261336483/10000000000 : ℝ)] ![(6721539842357/50000000000000 : ℝ), (4401481481973/10000000000000 : ℝ), (42542105479661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11069487/50000000 : ℝ)|^4119 ≤ (6721539842357/50000000000000 : ℝ)^3095
        have hw : |(-11069487/50000000 : ℝ)|=(11069487/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349402911/2500000000 : ℝ)|^4119 ≤ (4401481481973/10000000000000 : ℝ)^3095
        have hw : |(1349402911/2500000000 : ℝ)|=(1349402911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261336483/10000000000 : ℝ)|^4119 ≤ (42542105479661/100000000000000 : ℝ)^3095
        have hw : |(5261336483/10000000000 : ℝ)|=(5261336483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s5_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345742293/10000000000 : ℝ)*x 0 + (-2283088421/10000000000 : ℝ)*x 1 + (526133653/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345742293/10000000000 : ℝ)^4119 ≤ (43452801307907/100000000000000 : ℝ)^3095 := by
    have hnat : (5345742293 : ℕ)^4119*100000000000000^3095 ≤ 43452801307907^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345742293 10000000000 43452801307907 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283088421/10000000000 : ℝ)^4119 ≤ (7002546343527/50000000000000 : ℝ)^3095 := by
    have hnat : (2283088421 : ℕ)^4119*50000000000000^3095 ≤ 7002546343527^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283088421 10000000000 7002546343527 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526133653/1000000000 : ℝ)^4119 ≤ (42542105985429/100000000000000 : ℝ)^3095 := by
    have hnat : (526133653 : ℕ)^4119*100000000000000^3095 ≤ 42542105985429^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526133653 1000000000 42542105985429 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345742293/10000000000 : ℝ), (-2283088421/10000000000 : ℝ), (526133653/1000000000 : ℝ)] ![(43452801307907/100000000000000 : ℝ), (7002546343527/50000000000000 : ℝ), (42542105985429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345742293/10000000000 : ℝ)|^4119 ≤ (43452801307907/100000000000000 : ℝ)^3095
        have hw : |(5345742293/10000000000 : ℝ)|=(5345742293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2283088421/10000000000 : ℝ)|^4119 ≤ (7002546343527/50000000000000 : ℝ)^3095
        have hw : |(-2283088421/10000000000 : ℝ)|=(2283088421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526133653/1000000000 : ℝ)|^4119 ≤ (42542105985429/100000000000000 : ℝ)^3095
        have hw : |(526133653/1000000000 : ℝ)|=(526133653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s5_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672871143/5000000000 : ℝ)*x 0 + (328833531/625000000 : ℝ)*x 1 + (-91323539/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672871143/5000000000 : ℝ)^4119 ≤ (21726400616091/50000000000000 : ℝ)^3095 := by
    have hnat : (2672871143 : ℕ)^4119*50000000000000^3095 ≤ 21726400616091^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672871143 5000000000 21726400616091 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328833531/625000000 : ℝ)^4119 ≤ (21271052809777/50000000000000 : ℝ)^3095 := by
    have hnat : (328833531 : ℕ)^4119*50000000000000^3095 ≤ 21271052809777^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328833531 625000000 21271052809777 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91323539/400000000 : ℝ)^4119 ≤ (14005093127901/100000000000000 : ℝ)^3095 := by
    have hnat : (91323539 : ℕ)^4119*100000000000000^3095 ≤ 14005093127901^3095*400000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91323539 400000000 14005093127901 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672871143/5000000000 : ℝ), (328833531/625000000 : ℝ), (-91323539/400000000 : ℝ)] ![(21726400616091/50000000000000 : ℝ), (21271052809777/50000000000000 : ℝ), (14005093127901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672871143/5000000000 : ℝ)|^4119 ≤ (21726400616091/50000000000000 : ℝ)^3095
        have hw : |(2672871143/5000000000 : ℝ)|=(2672871143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328833531/625000000 : ℝ)|^4119 ≤ (21271052809777/50000000000000 : ℝ)^3095
        have hw : |(328833531/625000000 : ℝ)|=(328833531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91323539/400000000 : ℝ)|^4119 ≤ (14005093127901/100000000000000 : ℝ)^3095
        have hw : |(-91323539/400000000 : ℝ)|=(91323539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s5_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875674927/2000000000 : ℝ)*x 0 + (2123723453/5000000000 : ℝ)*x 1 + (2256707177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875674927/2000000000 : ℝ)^4119 ≤ (8328735615621/25000000000000 : ℝ)^3095 := by
    have hnat : (875674927 : ℕ)^4119*25000000000000^3095 ≤ 8328735615621^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875674927 2000000000 8328735615621 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123723453/5000000000 : ℝ)^4119 ≤ (3199571215279/10000000000000 : ℝ)^3095 := by
    have hnat : (2123723453 : ℕ)^4119*10000000000000^3095 ≤ 3199571215279^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123723453 5000000000 3199571215279 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256707177/5000000000 : ℝ)^4119 ≤ (34689345365661/100000000000000 : ℝ)^3095 := by
    have hnat : (2256707177 : ℕ)^4119*100000000000000^3095 ≤ 34689345365661^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256707177 5000000000 34689345365661 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875674927/2000000000 : ℝ), (2123723453/5000000000 : ℝ), (2256707177/5000000000 : ℝ)] ![(8328735615621/25000000000000 : ℝ), (3199571215279/10000000000000 : ℝ), (34689345365661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875674927/2000000000 : ℝ)|^4119 ≤ (8328735615621/25000000000000 : ℝ)^3095
        have hw : |(875674927/2000000000 : ℝ)|=(875674927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123723453/5000000000 : ℝ)|^4119 ≤ (3199571215279/10000000000000 : ℝ)^3095
        have hw : |(2123723453/5000000000 : ℝ)|=(2123723453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256707177/5000000000 : ℝ)|^4119 ≤ (34689345365661/100000000000000 : ℝ)^3095
        have hw : |(2256707177/5000000000 : ℝ)|=(2256707177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s5_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-138368929/625000000 : ℝ)*x 0 + (5261692161/10000000000 : ℝ)*x 1 + (5397254887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138368929/625000000 : ℝ)^4119 ≤ (672156192003/5000000000000 : ℝ)^3095 := by
    have hnat : (138368929 : ℕ)^4119*5000000000000^3095 ≤ 672156192003^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138368929 625000000 672156192003 5000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261692161/10000000000 : ℝ)^4119 ≤ (21272966492923/50000000000000 : ℝ)^3095 := by
    have hnat : (5261692161 : ℕ)^4119*50000000000000^3095 ≤ 21272966492923^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261692161 10000000000 21272966492923 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397254887/10000000000 : ℝ)^4119 ≤ (440109431693/1000000000000 : ℝ)^3095 := by
    have hnat : (5397254887 : ℕ)^4119*1000000000000^3095 ≤ 440109431693^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397254887 10000000000 440109431693 1000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138368929/625000000 : ℝ), (5261692161/10000000000 : ℝ), (5397254887/10000000000 : ℝ)] ![(672156192003/5000000000000 : ℝ), (21272966492923/50000000000000 : ℝ), (440109431693/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138368929/625000000 : ℝ)|^4119 ≤ (672156192003/5000000000000 : ℝ)^3095
        have hw : |(-138368929/625000000 : ℝ)|=(138368929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261692161/10000000000 : ℝ)|^4119 ≤ (21272966492923/50000000000000 : ℝ)^3095
        have hw : |(5261692161/10000000000 : ℝ)|=(5261692161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397254887/10000000000 : ℝ)|^4119 ≤ (440109431693/1000000000000 : ℝ)^3095
        have hw : |(5397254887/10000000000 : ℝ)|=(5397254887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s5_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311475749/10000000000 : ℝ)*x 0 + (-2147170237/10000000000 : ℝ)*x 1 + (2698627297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311475749/10000000000 : ℝ)^4119 ≤ (10770626166849/25000000000000 : ℝ)^3095 := by
    have hnat : (5311475749 : ℕ)^4119*25000000000000^3095 ≤ 10770626166849^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311475749 10000000000 10770626166849 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147170237/10000000000 : ℝ)^4119 ≤ (322663883133/2500000000000 : ℝ)^3095 := by
    have hnat : (2147170237 : ℕ)^4119*2500000000000^3095 ≤ 322663883133^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147170237 10000000000 322663883133 2500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698627297/5000000000 : ℝ)^4119 ≤ (44010939989597/100000000000000 : ℝ)^3095 := by
    have hnat : (2698627297 : ℕ)^4119*100000000000000^3095 ≤ 44010939989597^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698627297 5000000000 44010939989597 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311475749/10000000000 : ℝ), (-2147170237/10000000000 : ℝ), (2698627297/5000000000 : ℝ)] ![(10770626166849/25000000000000 : ℝ), (322663883133/2500000000000 : ℝ), (44010939989597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311475749/10000000000 : ℝ)|^4119 ≤ (10770626166849/25000000000000 : ℝ)^3095
        have hw : |(5311475749/10000000000 : ℝ)|=(5311475749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147170237/10000000000 : ℝ)|^4119 ≤ (322663883133/2500000000000 : ℝ)^3095
        have hw : |(-2147170237/10000000000 : ℝ)|=(2147170237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698627297/5000000000 : ℝ)|^4119 ≤ (44010939989597/100000000000000 : ℝ)^3095
        have hw : |(2698627297/5000000000 : ℝ)|=(2698627297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s5_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41495903/78125000 : ℝ)*x 0 + (5397254643/10000000000 : ℝ)*x 1 + (-2147170393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41495903/78125000 : ℝ)^4119 ≤ (8616500577249/20000000000000 : ℝ)^3095 := by
    have hnat : (41495903 : ℕ)^4119*20000000000000^3095 ≤ 8616500577249^3095*78125000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41495903 78125000 8616500577249 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397254643/10000000000 : ℝ)^4119 ≤ (11002735130339/25000000000000 : ℝ)^3095 := by
    have hnat : (5397254643 : ℕ)^4119*25000000000000^3095 ≤ 11002735130339^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397254643 10000000000 11002735130339 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147170393/10000000000 : ℝ)^4119 ≤ (12906556573277/100000000000000 : ℝ)^3095 := by
    have hnat : (2147170393 : ℕ)^4119*100000000000000^3095 ≤ 12906556573277^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147170393 10000000000 12906556573277 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41495903/78125000 : ℝ), (5397254643/10000000000 : ℝ), (-2147170393/10000000000 : ℝ)] ![(8616500577249/20000000000000 : ℝ), (11002735130339/25000000000000 : ℝ), (12906556573277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41495903/78125000 : ℝ)|^4119 ≤ (8616500577249/20000000000000 : ℝ)^3095
        have hw : |(41495903/78125000 : ℝ)|=(41495903/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397254643/10000000000 : ℝ)|^4119 ≤ (11002735130339/25000000000000 : ℝ)^3095
        have hw : |(5397254643/10000000000 : ℝ)|=(5397254643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147170393/10000000000 : ℝ)|^4119 ≤ (12906556573277/100000000000000 : ℝ)^3095
        have hw : |(-2147170393/10000000000 : ℝ)|=(2147170393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s5_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218919273/500000000 : ℝ)*x 0 + (70511257/156250000 : ℝ)*x 1 + (4248143927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218919273/500000000 : ℝ)^4119 ≤ (16657526040683/50000000000000 : ℝ)^3095 := by
    have hnat : (218919273 : ℕ)^4119*50000000000000^3095 ≤ 16657526040683^3095*500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218919273 500000000 16657526040683 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70511257/156250000 : ℝ)^4119 ≤ (17341123881903/50000000000000 : ℝ)^3095 := by
    have hnat : (70511257 : ℕ)^4119*50000000000000^3095 ≤ 17341123881903^3095*156250000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70511257 156250000 17341123881903 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248143927/10000000000 : ℝ)^4119 ≤ (32002700148231/100000000000000 : ℝ)^3095 := by
    have hnat : (4248143927 : ℕ)^4119*100000000000000^3095 ≤ 32002700148231^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248143927 10000000000 32002700148231 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218919273/500000000 : ℝ), (70511257/156250000 : ℝ), (4248143927/10000000000 : ℝ)] ![(16657526040683/50000000000000 : ℝ), (17341123881903/50000000000000 : ℝ), (32002700148231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218919273/500000000 : ℝ)|^4119 ≤ (16657526040683/50000000000000 : ℝ)^3095
        have hw : |(218919273/500000000 : ℝ)|=(218919273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70511257/156250000 : ℝ)|^4119 ≤ (17341123881903/50000000000000 : ℝ)^3095
        have hw : |(70511257/156250000 : ℝ)|=(70511257/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248143927/10000000000 : ℝ)|^4119 ≤ (32002700148231/100000000000000 : ℝ)^3095
        have hw : |(4248143927/10000000000 : ℝ)|=(4248143927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2791/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (343/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (343/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (343/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (343/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (343/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (343/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (343/3125 : ℝ) ^ (8237/2048 : ℝ) ≤ (13825867848909737/100000000000000000000 : ℝ) := by
    have hpowers : (343/3125 : ℝ)^8237 ≤ (13825867848909737/100000000000000000000 : ℝ)^2048 := by
      have hnat : (343 : ℕ)^8237*100000000000000000000^2048 ≤ 13825867848909737^2048*3125^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        343 3125 13825867848909737 100000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (343/3125 : ℝ)) (X := (13825867848909737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14247/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (39472874418828127/100000000000000000000 : ℝ) := by
    have hpowers : (14247/100000 : ℝ)^8237 ≤ (39472874418828127/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14247 : ℕ)^8237*100000000000000000000^2048 ≤ 39472874418828127^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14247 100000 39472874418828127 100000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14247/100000 : ℝ)) (X := (39472874418828127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013825867848909737/50000000000000000000 : ℝ) ≤ (2500171861335119/2500000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (50013825867848909737/50000000000000000000 : ℝ)^2048 ≤ (2500171861335119/2500000000000000 : ℝ)^8237 := by
      have hnat : (50013825867848909737 : ℕ)^2048*2500000000000000^8237 ≤ 2500171861335119^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013825867848909737 50000000000000000000 2500171861335119 2500000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500171861335119/2500000000000000 : ℝ)) (X := (50013825867848909737/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506662342783467233/12500000000000000000 : ℝ) ≤ (1000132492380997/1000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (12506662342783467233/12500000000000000000 : ℝ)^2048 ≤ (1000132492380997/1000000000000000 : ℝ)^8237 := by
      have hnat : (12506662342783467233 : ℕ)^2048*1000000000000000^8237 ≤ 1000132492380997^8237*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506662342783467233 12500000000000000000 1000132492380997 1000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000132492380997/1000000000000000 : ℝ)) (X := (12506662342783467233/12500000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039472874418828127/50000000000000000000 : ℝ) ≤ (1250245300284933/1250000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (50039472874418828127/50000000000000000000 : ℝ)^2048 ≤ (1250245300284933/1250000000000000 : ℝ)^8237 := by
      have hnat : (50039472874418828127 : ℕ)^2048*1250000000000000^8237 ≤ 1250245300284933^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039472874418828127 50000000000000000000 1250245300284933 1250000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250245300284933/1250000000000000 : ℝ)) (X := (50039472874418828127/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13825867848909737/100000000000000000000 : ℝ) ≤ ((8174563676586591177/8177500000000000000 : ℝ)+2*(318739234747/163550000000000 : ℝ)*(343/3125 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (8174563676586591177/8177500000000000000 : ℝ)+2*(318739234747/163550000000000 : ℝ)*(343/3125 : ℝ)=(2500171861335119/2500000000000000 : ℝ) by norm_num, show 1+2*(13825867848909737/100000000000000000000 : ℝ)=(50013825867848909737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39472874418828127/100000000000000000000 : ℝ)+(13825867848909737/100000000000000000000 : ℝ) ≤ ((8174563676586591177/8177500000000000000 : ℝ)+(318739234747/163550000000000 : ℝ)*((14247/100000 : ℝ)+(343/3125 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (8174563676586591177/8177500000000000000 : ℝ)+(318739234747/163550000000000 : ℝ)*((14247/100000 : ℝ)+(343/3125 : ℝ))=(1000132492380997/1000000000000000 : ℝ) by norm_num, show 1+(39472874418828127/100000000000000000000 : ℝ)+(13825867848909737/100000000000000000000 : ℝ)=(12506662342783467233/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39472874418828127/100000000000000000000 : ℝ) ≤ ((8174563676586591177/8177500000000000000 : ℝ)+2*(318739234747/163550000000000 : ℝ)*(14247/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (8174563676586591177/8177500000000000000 : ℝ)+2*(318739234747/163550000000000 : ℝ)*(14247/100000 : ℝ)=(1250245300284933/1250000000000000 : ℝ) by norm_num, show 1+2*(39472874418828127/100000000000000000000 : ℝ)=(50039472874418828127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8174563676586591177/8177500000000000000 : ℝ)*(X 1 0+X 2 0)+(318739234747/163550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (343/3125 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (8174563676586591177/8177500000000000000 : ℝ)) (alpha := (318739234747/163550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8174563676586591177/8177500000000000000 : ℝ)*(X 0 1+X 2 1)+(318739234747/163550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (343/3125 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (8174563676586591177/8177500000000000000 : ℝ)) (alpha := (318739234747/163550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8174563676586591177/8177500000000000000 : ℝ)*(X 0 2+X 1 2)+(318739234747/163550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (343/3125 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (8174563676586591177/8177500000000000000 : ℝ)) (alpha := (318739234747/163550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-11069487/50000000 : ℝ)*X 0 0+(1349402911/2500000000 : ℝ)*X 0 1+(5261336483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345742293/10000000000 : ℝ)*X 1 0+(-2283088421/10000000000 : ℝ)*X 1 1+(526133653/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672871143/5000000000 : ℝ)*X 2 0+(328833531/625000000 : ℝ)*X 2 1+(-91323539/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875674927/2000000000 : ℝ)*X 0 0+(2123723453/5000000000 : ℝ)*X 0 1+(2256707177/5000000000 : ℝ)*X 0 2+(875674927/2000000000 : ℝ)*X 1 0+(2123723453/5000000000 : ℝ)*X 1 1+(2256707177/5000000000 : ℝ)*X 1 2+(875674927/2000000000 : ℝ)*X 2 0+(2123723453/5000000000 : ℝ)*X 2 1+(2256707177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-138368929/625000000 : ℝ)*X 0 0+(5261692161/10000000000 : ℝ)*X 0 1+(5397254887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311475749/10000000000 : ℝ)*X 1 0+(-2147170237/10000000000 : ℝ)*X 1 1+(2698627297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41495903/78125000 : ℝ)*X 2 0+(5397254643/10000000000 : ℝ)*X 2 1+(-2147170393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218919273/500000000 : ℝ)*X 0 0+(70511257/156250000 : ℝ)*X 0 1+(4248143927/10000000000 : ℝ)*X 0 2+(218919273/500000000 : ℝ)*X 1 0+(70511257/156250000 : ℝ)*X 1 1+(4248143927/10000000000 : ℝ)*X 1 2+(218919273/500000000 : ℝ)*X 2 0+(70511257/156250000 : ℝ)*X 2 1+(4248143927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1464341811825396314894892003/204437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1372810033/100000000000000 : ℝ)*(base19) + (1243047211/100000000000000 : ℝ)*(base23) + (8028893/12500000000000 : ℝ)*(lower2) + (47141001/20000000000000 : ℝ)*(upper3) + (62367539/100000000000000 : ℝ)*(upper5) + (5549031898381887/100000000000000 : ℝ)*(major0) + (5549031898381887/100000000000000 : ℝ)*(major1) + (86703623412217/1562500000000 : ℝ)*(major2) + (917266711526193/12500000000000 : ℝ)*(sp0) + (7338165376942811/100000000000000 : ℝ)*(sp1) + (7338165506705633/100000000000000 : ℝ)*(sp2) + (1879937849215701/50000000000000 : ℝ)*(sp3) + (330575433/1000000000000 : ℝ)*(sp4) + (21109820023/100000000000000 : ℝ)*(sp7) + (117496775257857/3125000000000 : ℝ)*(f.failure) + (1834541687438211/25000000000000 : ℝ)*(f.sum) + (4944332213487/654200000000000000000000000 : ℝ)*base65 + (13503102027809610999/817750000000000000000000000000000 : ℝ)*base67 + (20581884402159443/25554687500000000000000000000000 : ℝ)*base69 + (12425319531561860999/817750000000000000000000000000000 : ℝ)*base71 + (274411104979/65420000000000000000000000 : ℝ)*base73 + (99424853046018733/6388671875000000000000000000000 : ℝ)*base76 + (6621763965208260999/817750000000000000000000000000000 : ℝ)*base77 + (5864688074579260999/817750000000000000000000000000000 : ℝ)*base79 + (3885060895627/4088750000000000000000000000 : ℝ)*base81 + (1248549/156250000000000000000 : ℝ)*base90 + (1248549/156250000000000000000 : ℝ)*base92 + (2811049/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2260334247008751558265595997/408875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24934301/50000000000000 : ℝ)*(base19) + (6553919/25000000000000 : ℝ)*(base23) + (1954343/100000000000000 : ℝ)*(lower2) + (9246943/20000000000000 : ℝ)*(lower3) + (111106203/100000000000000 : ℝ)*(lower4) + (41572047/25000000000000 : ℝ)*(lower5) + (5578147497470113/100000000000000 : ℝ)*(major0) + (5578147497470113/100000000000000 : ℝ)*(major1) + (5578147497470113/100000000000000 : ℝ)*(major2) + (675720061/6250000000000 : ℝ)*(sp0) + (737665912839943/10000000000000 : ℝ)*(sp4) + (1475333978010361/20000000000000 : ℝ)*(sp5) + (7376669913704731/100000000000000 : ℝ)*(sp6) + (3779624870747167/100000000000000 : ℝ)*(sp7) + (3779624870747167/100000000000000 : ℝ)*(f.failure) + (7376669939920407/100000000000000 : ℝ)*(f.sum) + (215492839679161/8177500000000000000000000000 : ℝ)*base65 + (5026400461205043001/817750000000000000000000000000000 : ℝ)*base67 + (11181029802698293001/817750000000000000000000000000000 : ℝ)*base69 + (10256169159348793001/817750000000000000000000000000000 : ℝ)*base71 + (25861189460817/16355000000000000000000000000 : ℝ)*base73 + (3236033825149706999/817750000000000000000000000000000 : ℝ)*base76 + (4465999547626543001/817750000000000000000000000000000 : ℝ)*base77 + (16239272728842206999/817750000000000000000000000000000 : ℝ)*base80 + (12430584748727/4088750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (36457719/5000000000000000000000 : ℝ)*base90 + (36457719/5000000000000000000000 : ℝ)*base92 + (36457719/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1045_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1045_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1045_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1045_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1045_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1045_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1045_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
