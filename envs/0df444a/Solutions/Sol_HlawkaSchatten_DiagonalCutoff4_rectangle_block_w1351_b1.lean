-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:58.231131+00:00
-- url     : https://prove2.me/submissions/fb7d43cb-f44b-4460-b79f-900479a216b2

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
theorem support_rectangle_w1351_s3_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017275561/5000000000 : ℝ)*x 0 + (2713016791/5000000000 : ℝ)*x 1 + (5232187073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017275561/5000000000 : ℝ)^4311 ≤ (6194491323613/50000000000000 : ℝ)^3287 := by
    have hnat : (1017275561 : ℕ)^4311*50000000000000^3287 ≤ 6194491323613^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017275561 5000000000 6194491323613 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713016791/5000000000 : ℝ)^4311 ≤ (897006783247/2000000000000 : ℝ)^3287 := by
    have hnat : (2713016791 : ℕ)^4311*2000000000000^3287 ≤ 897006783247^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713016791 5000000000 897006783247 2000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232187073/10000000000 : ℝ)^4311 ≤ (21380339085841/50000000000000 : ℝ)^3287 := by
    have hnat : (5232187073 : ℕ)^4311*50000000000000^3287 ≤ 21380339085841^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232187073 10000000000 21380339085841 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017275561/5000000000 : ℝ), (2713016791/5000000000 : ℝ), (5232187073/10000000000 : ℝ)] ![(6194491323613/50000000000000 : ℝ), (897006783247/2000000000000 : ℝ), (21380339085841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017275561/5000000000 : ℝ)|^4311 ≤ (6194491323613/50000000000000 : ℝ)^3287
        have hw : |(-1017275561/5000000000 : ℝ)|=(1017275561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713016791/5000000000 : ℝ)|^4311 ≤ (897006783247/2000000000000 : ℝ)^3287
        have hw : |(2713016791/5000000000 : ℝ)|=(2713016791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232187073/10000000000 : ℝ)|^4311 ≤ (21380339085841/50000000000000 : ℝ)^3287
        have hw : |(5232187073/10000000000 : ℝ)|=(5232187073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s3_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338090723/2500000000 : ℝ)*x 0 + (-2133598729/10000000000 : ℝ)*x 1 + (5232186997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338090723/2500000000 : ℝ)^4311 ≤ (440533838323/1000000000000 : ℝ)^3287 := by
    have hnat : (1338090723 : ℕ)^4311*1000000000000^3287 ≤ 440533838323^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338090723 2500000000 440533838323 1000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2133598729/10000000000 : ℝ)^4311 ≤ (13185938791759/100000000000000 : ℝ)^3287 := by
    have hnat : (2133598729 : ℕ)^4311*100000000000000^3287 ≤ 13185938791759^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133598729 10000000000 13185938791759 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232186997/10000000000 : ℝ)^4311 ≤ (21380338678533/50000000000000 : ℝ)^3287 := by
    have hnat : (5232186997 : ℕ)^4311*50000000000000^3287 ≤ 21380338678533^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232186997 10000000000 21380338678533 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338090723/2500000000 : ℝ), (-2133598729/10000000000 : ℝ), (5232186997/10000000000 : ℝ)] ![(440533838323/1000000000000 : ℝ), (13185938791759/100000000000000 : ℝ), (21380338678533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338090723/2500000000 : ℝ)|^4311 ≤ (440533838323/1000000000000 : ℝ)^3287
        have hw : |(1338090723/2500000000 : ℝ)|=(1338090723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2133598729/10000000000 : ℝ)|^4311 ≤ (13185938791759/100000000000000 : ℝ)^3287
        have hw : |(-2133598729/10000000000 : ℝ)|=(2133598729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232186997/10000000000 : ℝ)|^4311 ≤ (21380338678533/50000000000000 : ℝ)^3287
        have hw : |(5232186997/10000000000 : ℝ)|=(5232186997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s3_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352362881/10000000000 : ℝ)*x 0 + (130804659/250000000 : ℝ)*x 1 + (-1066799793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352362881/10000000000 : ℝ)^4311 ≤ (22026691856779/50000000000000 : ℝ)^3287 := by
    have hnat : (5352362881 : ℕ)^4311*50000000000000^3287 ≤ 22026691856779^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352362881 10000000000 22026691856779 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130804659/250000000 : ℝ)^4311 ≤ (42760670529293/100000000000000 : ℝ)^3287 := by
    have hnat : (130804659 : ℕ)^4311*100000000000000^3287 ≤ 42760670529293^3287*250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130804659 250000000 42760670529293 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066799793/5000000000 : ℝ)^4311 ≤ (6592972869061/50000000000000 : ℝ)^3287 := by
    have hnat : (1066799793 : ℕ)^4311*50000000000000^3287 ≤ 6592972869061^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066799793 5000000000 6592972869061 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352362881/10000000000 : ℝ), (130804659/250000000 : ℝ), (-1066799793/5000000000 : ℝ)] ![(22026691856779/50000000000000 : ℝ), (42760670529293/100000000000000 : ℝ), (6592972869061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352362881/10000000000 : ℝ)|^4311 ≤ (22026691856779/50000000000000 : ℝ)^3287
        have hw : |(5352362881/10000000000 : ℝ)|=(5352362881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130804659/250000000 : ℝ)|^4311 ≤ (42760670529293/100000000000000 : ℝ)^3287
        have hw : |(130804659/250000000 : ℝ)|=(130804659/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066799793/5000000000 : ℝ)|^4311 ≤ (6592972869061/50000000000000 : ℝ)^3287
        have hw : |(-1066799793/5000000000 : ℝ)|=(1066799793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s3_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323260693/10000000000 : ℝ)*x 0 + (103100601/250000000 : ℝ)*x 1 + (4531425421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323260693/10000000000 : ℝ)^4311 ≤ (33293209125397/100000000000000 : ℝ)^3287 := by
    have hnat : (4323260693 : ℕ)^4311*100000000000000^3287 ≤ 33293209125397^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323260693 10000000000 33293209125397 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103100601/250000000 : ℝ)^4311 ≤ (15647757180581/50000000000000 : ℝ)^3287 := by
    have hnat : (103100601 : ℕ)^4311*50000000000000^3287 ≤ 15647757180581^3287*250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103100601 250000000 15647757180581 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531425421/10000000000 : ℝ)^4311 ≤ (35411276489423/100000000000000 : ℝ)^3287 := by
    have hnat : (4531425421 : ℕ)^4311*100000000000000^3287 ≤ 35411276489423^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531425421 10000000000 35411276489423 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323260693/10000000000 : ℝ), (103100601/250000000 : ℝ), (4531425421/10000000000 : ℝ)] ![(33293209125397/100000000000000 : ℝ), (15647757180581/50000000000000 : ℝ), (35411276489423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323260693/10000000000 : ℝ)|^4311 ≤ (33293209125397/100000000000000 : ℝ)^3287
        have hw : |(4323260693/10000000000 : ℝ)|=(4323260693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103100601/250000000 : ℝ)|^4311 ≤ (15647757180581/50000000000000 : ℝ)^3287
        have hw : |(103100601/250000000 : ℝ)|=(103100601/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531425421/10000000000 : ℝ)|^4311 ≤ (35411276489423/100000000000000 : ℝ)^3287
        have hw : |(4531425421/10000000000 : ℝ)|=(4531425421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s3_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017284879/5000000000 : ℝ)*x 0 + (1308247621/2500000000 : ℝ)*x 1 + (2712612729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017284879/5000000000 : ℝ)^4311 ≤ (6194565740017/50000000000000 : ℝ)^3287 := by
    have hnat : (1017284879 : ℕ)^4311*50000000000000^3287 ≤ 6194565740017^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017284879 5000000000 6194565740017 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308247621/2500000000 : ℝ)^4311 ≤ (42769289850031/100000000000000 : ℝ)^3287 := by
    have hnat : (1308247621 : ℕ)^4311*100000000000000^3287 ≤ 42769289850031^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308247621 2500000000 42769289850031 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712612729/5000000000 : ℝ)^4311 ≤ (280259866563/625000000000 : ℝ)^3287 := by
    have hnat : (2712612729 : ℕ)^4311*625000000000^3287 ≤ 280259866563^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712612729 5000000000 280259866563 625000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017284879/5000000000 : ℝ), (1308247621/2500000000 : ℝ), (2712612729/5000000000 : ℝ)] ![(6194565740017/50000000000000 : ℝ), (42769289850031/100000000000000 : ℝ), (280259866563/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017284879/5000000000 : ℝ)|^4311 ≤ (6194565740017/50000000000000 : ℝ)^3287
        have hw : |(-1017284879/5000000000 : ℝ)|=(1017284879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308247621/2500000000 : ℝ)|^4311 ≤ (42769289850031/100000000000000 : ℝ)^3287
        have hw : |(1308247621/2500000000 : ℝ)|=(1308247621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712612729/5000000000 : ℝ)|^4311 ≤ (280259866563/625000000000 : ℝ)^3287
        have hw : |(2712612729/5000000000 : ℝ)|=(2712612729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s3_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325595003/2500000000 : ℝ)*x 0 + (-12128501/62500000 : ℝ)*x 1 + (1356306363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325595003/2500000000 : ℝ)^4311 ≤ (43514618344549/100000000000000 : ℝ)^3287 := by
    have hnat : (1325595003 : ℕ)^4311*100000000000000^3287 ≤ 43514618344549^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325595003 2500000000 43514618344549 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12128501/62500000 : ℝ)^4311 ≤ (11643803054539/100000000000000 : ℝ)^3287 := by
    have hnat : (12128501 : ℕ)^4311*100000000000000^3287 ≤ 11643803054539^3287*62500000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12128501 62500000 11643803054539 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356306363/2500000000 : ℝ)^4311 ≤ (22420789292519/50000000000000 : ℝ)^3287 := by
    have hnat : (1356306363 : ℕ)^4311*50000000000000^3287 ≤ 22420789292519^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356306363 2500000000 22420789292519 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325595003/2500000000 : ℝ), (-12128501/62500000 : ℝ), (1356306363/2500000000 : ℝ)] ![(43514618344549/100000000000000 : ℝ), (11643803054539/100000000000000 : ℝ), (22420789292519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325595003/2500000000 : ℝ)|^4311 ≤ (43514618344549/100000000000000 : ℝ)^3287
        have hw : |(1325595003/2500000000 : ℝ)|=(1325595003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12128501/62500000 : ℝ)|^4311 ≤ (11643803054539/100000000000000 : ℝ)^3287
        have hw : |(-12128501/62500000 : ℝ)|=(12128501/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356306363/2500000000 : ℝ)|^4311 ≤ (22420789292519/50000000000000 : ℝ)^3287
        have hw : |(1356306363/2500000000 : ℝ)|=(1356306363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s3_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530237981/1000000000 : ℝ)*x 0 + (678153199/1250000000 : ℝ)*x 1 + (-485140061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530237981/1000000000 : ℝ)^4311 ≤ (43514616170377/100000000000000 : ℝ)^3287 := by
    have hnat : (530237981 : ℕ)^4311*100000000000000^3287 ≤ 43514616170377^3287*1000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530237981 1000000000 43514616170377 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678153199/1250000000 : ℝ)^4311 ≤ (1121039502567/2500000000000 : ℝ)^3287 := by
    have hnat : (678153199 : ℕ)^4311*2500000000000^3287 ≤ 1121039502567^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678153199 1250000000 1121039502567 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485140061/2500000000 : ℝ)^4311 ≤ (465752148623/4000000000000 : ℝ)^3287 := by
    have hnat : (485140061 : ℕ)^4311*4000000000000^3287 ≤ 465752148623^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485140061 2500000000 465752148623 4000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530237981/1000000000 : ℝ), (678153199/1250000000 : ℝ), (-485140061/2500000000 : ℝ)] ![(43514616170377/100000000000000 : ℝ), (1121039502567/2500000000000 : ℝ), (465752148623/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530237981/1000000000 : ℝ)|^4311 ≤ (43514616170377/100000000000000 : ℝ)^3287
        have hw : |(530237981/1000000000 : ℝ)|=(530237981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678153199/1250000000 : ℝ)|^4311 ≤ (1121039502567/2500000000000 : ℝ)^3287
        have hw : |(678153199/1250000000 : ℝ)|=(678153199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485140061/2500000000 : ℝ)|^4311 ≤ (465752148623/4000000000000 : ℝ)^3287
        have hw : |(-485140061/2500000000 : ℝ)|=(485140061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s3_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270206231/625000000 : ℝ)*x 0 + (2264868441/5000000000 : ℝ)*x 1 + (103143077/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270206231/625000000 : ℝ)^4311 ≤ (832340076433/2500000000000 : ℝ)^3287 := by
    have hnat : (270206231 : ℕ)^4311*2500000000000^3287 ≤ 832340076433^3287*625000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270206231 625000000 832340076433 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264868441/5000000000 : ℝ)^4311 ≤ (35393971515473/100000000000000 : ℝ)^3287 := by
    have hnat : (2264868441 : ℕ)^4311*100000000000000^3287 ≤ 35393971515473^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264868441 5000000000 35393971515473 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103143077/250000000 : ℝ)^4311 ≤ (15656212707931/50000000000000 : ℝ)^3287 := by
    have hnat : (103143077 : ℕ)^4311*50000000000000^3287 ≤ 15656212707931^3287*250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103143077 250000000 15656212707931 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270206231/625000000 : ℝ), (2264868441/5000000000 : ℝ), (103143077/250000000 : ℝ)] ![(832340076433/2500000000000 : ℝ), (35393971515473/100000000000000 : ℝ), (15656212707931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270206231/625000000 : ℝ)|^4311 ≤ (832340076433/2500000000000 : ℝ)^3287
        have hw : |(270206231/625000000 : ℝ)|=(270206231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264868441/5000000000 : ℝ)|^4311 ≤ (35393971515473/100000000000000 : ℝ)^3287
        have hw : |(2264868441/5000000000 : ℝ)|=(2264868441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103143077/250000000 : ℝ)|^4311 ≤ (15656212707931/50000000000000 : ℝ)^3287
        have hw : |(103143077/250000000 : ℝ)|=(103143077/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10899/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (991/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (991/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (991/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (991/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (991/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (991/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (991/10000 : ℝ) ^ (2155/512 : ℝ) ≤ (297481321725661/5000000000000000000 : ℝ) := by
    have hpowers : (991/10000 : ℝ)^2155 ≤ (297481321725661/5000000000000000000 : ℝ)^512 := by
      have hnat : (991 : ℕ)^2155*5000000000000000000^512 ≤ 297481321725661^512*10000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        991 10000 297481321725661 5000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (991/10000 : ℝ)) (X := (297481321725661/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16069/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (45500846801000071/100000000000000000000 : ℝ) := by
    have hpowers : (16069/100000 : ℝ)^2155 ≤ (45500846801000071/100000000000000000000 : ℝ)^512 := by
      have hnat : (16069 : ℕ)^2155*100000000000000000000^512 ≤ 45500846801000071^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16069 100000 45500846801000071 100000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16069/100000 : ℝ)) (X := (45500846801000071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500297481321725661/2500000000000000000 : ℝ) ≤ (156254417155693/156250000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (2500297481321725661/2500000000000000000 : ℝ)^512 ≤ (156254417155693/156250000000000 : ℝ)^2155 := by
      have hnat : (2500297481321725661 : ℕ)^512*156250000000000^2155 ≤ 156254417155693^2155*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500297481321725661 2500000000000000000 156254417155693 156250000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156254417155693/156250000000000 : ℝ)) (X := (2500297481321725661/2500000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051450473235513291/100000000000000000000 : ℝ) ≤ (10001222156714997/10000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (100051450473235513291/100000000000000000000 : ℝ)^512 ≤ (10001222156714997/10000000000000000 : ℝ)^2155 := by
      have hnat : (100051450473235513291 : ℕ)^512*10000000000000000^2155 ≤ 10001222156714997^2155*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051450473235513291 100000000000000000000 10001222156714997 10000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001222156714997/10000000000000000 : ℝ)) (X := (100051450473235513291/100000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045500846801000071/50000000000000000000 : ℝ) ≤ (5001080807732821/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (50045500846801000071/50000000000000000000 : ℝ)^512 ≤ (5001080807732821/5000000000000000 : ℝ)^2155 := by
      have hnat : (50045500846801000071 : ℕ)^512*5000000000000000^2155 ≤ 5001080807732821^2155*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045500846801000071 50000000000000000000 5001080807732821 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001080807732821/5000000000000000 : ℝ)) (X := (50045500846801000071/50000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(297481321725661/5000000000000000000 : ℝ) ≤ ((15393280266081165017/15397500000000000000 : ℝ)+2*(187891750129/123180000000000 : ℝ)*(991/10000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (15393280266081165017/15397500000000000000 : ℝ)+2*(187891750129/123180000000000 : ℝ)*(991/10000 : ℝ)=(156254417155693/156250000000000 : ℝ) by norm_num, show 1+2*(297481321725661/5000000000000000000 : ℝ)=(2500297481321725661/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45500846801000071/100000000000000000000 : ℝ)+(297481321725661/5000000000000000000 : ℝ) ≤ ((15393280266081165017/15397500000000000000 : ℝ)+(187891750129/123180000000000 : ℝ)*((16069/100000 : ℝ)+(991/10000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (15393280266081165017/15397500000000000000 : ℝ)+(187891750129/123180000000000 : ℝ)*((16069/100000 : ℝ)+(991/10000 : ℝ))=(10001222156714997/10000000000000000 : ℝ) by norm_num, show 1+(45500846801000071/100000000000000000000 : ℝ)+(297481321725661/5000000000000000000 : ℝ)=(100051450473235513291/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45500846801000071/100000000000000000000 : ℝ) ≤ ((15393280266081165017/15397500000000000000 : ℝ)+2*(187891750129/123180000000000 : ℝ)*(16069/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (15393280266081165017/15397500000000000000 : ℝ)+2*(187891750129/123180000000000 : ℝ)*(16069/100000 : ℝ)=(5001080807732821/5000000000000000 : ℝ) by norm_num, show 1+2*(45500846801000071/100000000000000000000 : ℝ)=(50045500846801000071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15393280266081165017/15397500000000000000 : ℝ)*(X 1 0+X 2 0)+(187891750129/123180000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (991/10000 : ℝ)) (hi := (16069/100000 : ℝ)) (c := (15393280266081165017/15397500000000000000 : ℝ)) (alpha := (187891750129/123180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15393280266081165017/15397500000000000000 : ℝ)*(X 0 1+X 2 1)+(187891750129/123180000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (991/10000 : ℝ)) (hi := (16069/100000 : ℝ)) (c := (15393280266081165017/15397500000000000000 : ℝ)) (alpha := (187891750129/123180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15393280266081165017/15397500000000000000 : ℝ)*(X 0 2+X 1 2)+(187891750129/123180000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (991/10000 : ℝ)) (hi := (16069/100000 : ℝ)) (c := (15393280266081165017/15397500000000000000 : ℝ)) (alpha := (187891750129/123180000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1017275561/5000000000 : ℝ)*X 0 0+(2713016791/5000000000 : ℝ)*X 0 1+(5232187073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338090723/2500000000 : ℝ)*X 1 0+(-2133598729/10000000000 : ℝ)*X 1 1+(5232186997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352362881/10000000000 : ℝ)*X 2 0+(130804659/250000000 : ℝ)*X 2 1+(-1066799793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323260693/10000000000 : ℝ)*X 0 0+(103100601/250000000 : ℝ)*X 0 1+(4531425421/10000000000 : ℝ)*X 0 2+(4323260693/10000000000 : ℝ)*X 1 0+(103100601/250000000 : ℝ)*X 1 1+(4531425421/10000000000 : ℝ)*X 1 2+(4323260693/10000000000 : ℝ)*X 2 0+(103100601/250000000 : ℝ)*X 2 1+(4531425421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1017284879/5000000000 : ℝ)*X 0 0+(1308247621/2500000000 : ℝ)*X 0 1+(2712612729/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325595003/2500000000 : ℝ)*X 1 0+(-12128501/62500000 : ℝ)*X 1 1+(1356306363/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530237981/1000000000 : ℝ)*X 2 0+(678153199/1250000000 : ℝ)*X 2 1+(-485140061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270206231/625000000 : ℝ)*X 0 0+(2264868441/5000000000 : ℝ)*X 0 1+(103143077/250000000 : ℝ)*X 0 2+(270206231/625000000 : ℝ)*X 1 0+(2264868441/5000000000 : ℝ)*X 1 1+(103143077/250000000 : ℝ)*X 1 2+(270206231/625000000 : ℝ)*X 2 0+(2264868441/5000000000 : ℝ)*X 2 1+(103143077/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116422612448575280141069577/32078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (817463791/100000000000000 : ℝ)*(base19) + (203894207/25000000000000 : ℝ)*(base23) + (160048841/50000000000000 : ℝ)*(upper3) + (1768461/2500000000000 : ℝ)*(lower4) + (475833071863023/12500000000000 : ℝ)*(major0) + (475833071863023/12500000000000 : ℝ)*(major1) + (475833071863023/12500000000000 : ℝ)*(major2) + (5158734949945141/100000000000000 : ℝ)*(sp0) + (2579367854875771/50000000000000 : ℝ)*(sp1) + (5158722492402487/100000000000000 : ℝ)*(sp2) + (1227292736763577/50000000000000 : ℝ)*(sp3) + (1577270191/100000000000000 : ℝ)*(sp4) + (13219236017/100000000000000 : ℝ)*(sp6) + (7028087677/100000000000000 : ℝ)*(sp7) + (2454592501614831/100000000000000 : ℝ)*(f.failure) + (5158736527215333/100000000000000 : ℝ)*(f.sum) + (79896994941/205300000000000000000000000 : ℝ)*base65 + (499086401326238797/64156250000000000000000000000000 : ℝ)*base67 + (730961268319832547/64156250000000000000000000000000 : ℝ)*base69 + (236737983898301297/64156250000000000000000000000000 : ℝ)*base71 + (354605093839/513250000000000000000000000 : ℝ)*base74 + (25498206446113797/64156250000000000000000000000000 : ℝ)*base75 + (226734590438645047/64156250000000000000000000000000 : ℝ)*base77 + (633529872872051297/64156250000000000000000000000000 : ℝ)*base79 + (161022199083/51325000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (10270911/5000000000000000000000 : ℝ)*base89 + (10270911/5000000000000000000000 : ℝ)*base91 + (10270911/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (739250904094080519594231327/128312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (564333511/50000000000000 : ℝ)*(base19) + (496742899/50000000000000 : ℝ)*(base23) + (103747691/100000000000000 : ℝ)*(upper3) + (22524141/50000000000000 : ℝ)*(lower4) + (2115393/1562500000000 : ℝ)*(upper5) + (1919281884397569/50000000000000 : ℝ)*(major0) + (1919281884397569/50000000000000 : ℝ)*(major1) + (1919281884397569/50000000000000 : ℝ)*(major2) + (4242375913/20000000000000 : ℝ)*(sp1) + (377632933/2000000000000 : ℝ)*(sp2) + (2600982890640053/50000000000000 : ℝ)*(sp4) + (65024293009169/1250000000000 : ℝ)*(sp5) + (5201945906147657/100000000000000 : ℝ)*(sp6) + (618790391066441/25000000000000 : ℝ)*(sp7) + (618790391066441/25000000000000 : ℝ)*(f.failure) + (2600982890640053/50000000000000 : ℝ)*(f.sum) + (7591741954473/1026500000000000000000000000 : ℝ)*base65 + (360190309291077109/256625000000000000000000000000000 : ℝ)*base68 + (1284095238790422891/256625000000000000000000000000000 : ℝ)*base69 + (24595060329422891/256625000000000000000000000000000 : ℝ)*base71 + (3448406072299/410600000000000000000000000 : ℝ)*base73 + (583218301239702109/256625000000000000000000000000000 : ℝ)*base76 + (889909000479422891/256625000000000000000000000000000 : ℝ)*base77 + (840706743968922891/256625000000000000000000000000000 : ℝ)*base79 + (1214482888799/1026500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (7172679/1250000000000000000000 : ℝ)*base90 + (7172679/1250000000000000000000 : ℝ)*base92 + (7172679/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1351_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1351_s4_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017970627/5000000000 : ℝ)*x 0 + (5414642817/10000000000 : ℝ)*x 1 + (1048532951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017970627/5000000000 : ℝ)^4311 ≤ (1550010729133/12500000000000 : ℝ)^3287 := by
    have hnat : (1017970627 : ℕ)^4311*12500000000000^3287 ≤ 1550010729133^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017970627 5000000000 1550010729133 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414642817/10000000000 : ℝ)^4311 ≤ (44726894487113/100000000000000 : ℝ)^3287 := by
    have hnat : (5414642817 : ℕ)^4311*100000000000000^3287 ≤ 44726894487113^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414642817 10000000000 44726894487113 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048532951/2000000000 : ℝ)^4311 ≤ (10718254919171/25000000000000 : ℝ)^3287 := by
    have hnat : (1048532951 : ℕ)^4311*25000000000000^3287 ≤ 10718254919171^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048532951 2000000000 10718254919171 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017970627/5000000000 : ℝ), (5414642817/10000000000 : ℝ), (1048532951/2000000000 : ℝ)] ![(1550010729133/12500000000000 : ℝ), (44726894487113/100000000000000 : ℝ), (10718254919171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017970627/5000000000 : ℝ)|^4311 ≤ (1550010729133/12500000000000 : ℝ)^3287
        have hw : |(-1017970627/5000000000 : ℝ)|=(1017970627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414642817/10000000000 : ℝ)|^4311 ≤ (44726894487113/100000000000000 : ℝ)^3287
        have hw : |(5414642817/10000000000 : ℝ)|=(5414642817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048532951/2000000000 : ℝ)|^4311 ≤ (10718254919171/25000000000000 : ℝ)^3287
        have hw : |(1048532951/2000000000 : ℝ)|=(1048532951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s4_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349455701/10000000000 : ℝ)*x 0 + (-2123602789/10000000000 : ℝ)*x 1 + (5242664727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349455701/10000000000 : ℝ)^4311 ≤ (440220041273/1000000000000 : ℝ)^3287 := by
    have hnat : (5349455701 : ℕ)^4311*1000000000000^3287 ≤ 440220041273^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349455701 10000000000 440220041273 1000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123602789/10000000000 : ℝ)^4311 ≤ (13104976483419/100000000000000 : ℝ)^3287 := by
    have hnat : (2123602789 : ℕ)^4311*100000000000000^3287 ≤ 13104976483419^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123602789 10000000000 13104976483419 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242664727/10000000000 : ℝ)^4311 ≤ (342984155011/800000000000 : ℝ)^3287 := by
    have hnat : (5242664727 : ℕ)^4311*800000000000^3287 ≤ 342984155011^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242664727 10000000000 342984155011 800000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349455701/10000000000 : ℝ), (-2123602789/10000000000 : ℝ), (5242664727/10000000000 : ℝ)] ![(440220041273/1000000000000 : ℝ), (13104976483419/100000000000000 : ℝ), (342984155011/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349455701/10000000000 : ℝ)|^4311 ≤ (440220041273/1000000000000 : ℝ)^3287
        have hw : |(5349455701/10000000000 : ℝ)|=(5349455701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123602789/10000000000 : ℝ)|^4311 ≤ (13104976483419/100000000000000 : ℝ)^3287
        have hw : |(-2123602789/10000000000 : ℝ)|=(2123602789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242664727/10000000000 : ℝ)|^4311 ≤ (342984155011/800000000000 : ℝ)^3287
        have hw : |(5242664727/10000000000 : ℝ)|=(5242664727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s4_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349455699/10000000000 : ℝ)*x 0 + (5242664747/10000000000 : ℝ)*x 1 + (-424720553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349455699/10000000000 : ℝ)^4311 ≤ (22011002052857/50000000000000 : ℝ)^3287 := by
    have hnat : (5349455699 : ℕ)^4311*50000000000000^3287 ≤ 22011002052857^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349455699 10000000000 22011002052857 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242664747/10000000000 : ℝ)^4311 ≤ (21436509795441/50000000000000 : ℝ)^3287 := by
    have hnat : (5242664747 : ℕ)^4311*50000000000000^3287 ≤ 21436509795441^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242664747 10000000000 21436509795441 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424720553/2000000000 : ℝ)^4311 ≤ (13104976289173/100000000000000 : ℝ)^3287 := by
    have hnat : (424720553 : ℕ)^4311*100000000000000^3287 ≤ 13104976289173^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424720553 2000000000 13104976289173 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349455699/10000000000 : ℝ), (5242664747/10000000000 : ℝ), (-424720553/2000000000 : ℝ)] ![(22011002052857/50000000000000 : ℝ), (21436509795441/50000000000000 : ℝ), (13104976289173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349455699/10000000000 : ℝ)|^4311 ≤ (22011002052857/50000000000000 : ℝ)^3287
        have hw : |(5349455699/10000000000 : ℝ)|=(5349455699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242664747/10000000000 : ℝ)|^4311 ≤ (21436509795441/50000000000000 : ℝ)^3287
        have hw : |(5242664747/10000000000 : ℝ)|=(5242664747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424720553/2000000000 : ℝ)|^4311 ≤ (13104976289173/100000000000000 : ℝ)^3287
        have hw : |(-424720553/2000000000 : ℝ)|=(424720553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s4_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324105473/10000000000 : ℝ)*x 0 + (2073450101/5000000000 : ℝ)*x 1 + (2254170427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324105473/10000000000 : ℝ)^4311 ≤ (16650870843127/50000000000000 : ℝ)^3287 := by
    have hnat : (4324105473 : ℕ)^4311*50000000000000^3287 ≤ 16650870843127^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324105473 10000000000 16650870843127 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073450101/5000000000 : ℝ)^4311 ≤ (1970211845381/6250000000000 : ℝ)^3287 := by
    have hnat : (2073450101 : ℕ)^4311*6250000000000^3287 ≤ 1970211845381^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073450101 5000000000 1970211845381 6250000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254170427/5000000000 : ℝ)^4311 ≤ (4396858597469/12500000000000 : ℝ)^3287 := by
    have hnat : (2254170427 : ℕ)^4311*12500000000000^3287 ≤ 4396858597469^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254170427 5000000000 4396858597469 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324105473/10000000000 : ℝ), (2073450101/5000000000 : ℝ), (2254170427/5000000000 : ℝ)] ![(16650870843127/50000000000000 : ℝ), (1970211845381/6250000000000 : ℝ), (4396858597469/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324105473/10000000000 : ℝ)|^4311 ≤ (16650870843127/50000000000000 : ℝ)^3287
        have hw : |(4324105473/10000000000 : ℝ)|=(4324105473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073450101/5000000000 : ℝ)|^4311 ≤ (1970211845381/6250000000000 : ℝ)^3287
        have hw : |(2073450101/5000000000 : ℝ)|=(2073450101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254170427/5000000000 : ℝ)|^4311 ≤ (4396858597469/12500000000000 : ℝ)^3287
        have hw : |(2254170427/5000000000 : ℝ)|=(2254170427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s4_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-127247149/625000000 : ℝ)*x 0 + (81926529/156250000 : ℝ)*x 1 + (676750793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127247149/625000000 : ℝ)^4311 ≤ (620009535777/5000000000000 : ℝ)^3287 := by
    have hnat : (127247149 : ℕ)^4311*5000000000000^3287 ≤ 620009535777^3287*625000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127247149 625000000 620009535777 5000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81926529/156250000 : ℝ)^4311 ≤ (21439905007971/50000000000000 : ℝ)^3287 := by
    have hnat : (81926529 : ℕ)^4311*50000000000000^3287 ≤ 21439905007971^3287*156250000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81926529 156250000 21439905007971 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676750793/1250000000 : ℝ)^4311 ≤ (44719999248757/100000000000000 : ℝ)^3287 := by
    have hnat : (676750793 : ℕ)^4311*100000000000000^3287 ≤ 44719999248757^3287*1250000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676750793 1250000000 44719999248757 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127247149/625000000 : ℝ), (81926529/156250000 : ℝ), (676750793/1250000000 : ℝ)] ![(620009535777/5000000000000 : ℝ), (21439905007971/50000000000000 : ℝ), (44719999248757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127247149/625000000 : ℝ)|^4311 ≤ (620009535777/5000000000000 : ℝ)^3287
        have hw : |(-127247149/625000000 : ℝ)|=(127247149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81926529/156250000 : ℝ)|^4311 ≤ (21439905007971/50000000000000 : ℝ)^3287
        have hw : |(81926529/156250000 : ℝ)|=(81926529/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676750793/1250000000 : ℝ)|^4311 ≤ (44719999248757/100000000000000 : ℝ)^3287
        have hw : |(676750793/1250000000 : ℝ)|=(676750793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s4_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305112107/10000000000 : ℝ)*x 0 + (-9761307/50000000 : ℝ)*x 1 + (5414006507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305112107/10000000000 : ℝ)^4311 ≤ (43544026873091/100000000000000 : ℝ)^3287 := by
    have hnat : (5305112107 : ℕ)^4311*100000000000000^3287 ≤ 43544026873091^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305112107 10000000000 43544026873091 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9761307/50000000 : ℝ)^4311 ≤ (11735972101599/100000000000000 : ℝ)^3287 := by
    have hnat : (9761307 : ℕ)^4311*100000000000000^3287 ≤ 11735972101599^3287*50000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9761307 50000000 11735972101599 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414006507/10000000000 : ℝ)^4311 ≤ (11180000253647/25000000000000 : ℝ)^3287 := by
    have hnat : (5414006507 : ℕ)^4311*25000000000000^3287 ≤ 11180000253647^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414006507 10000000000 11180000253647 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305112107/10000000000 : ℝ), (-9761307/50000000 : ℝ), (5414006507/10000000000 : ℝ)] ![(43544026873091/100000000000000 : ℝ), (11735972101599/100000000000000 : ℝ), (11180000253647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305112107/10000000000 : ℝ)|^4311 ≤ (43544026873091/100000000000000 : ℝ)^3287
        have hw : |(5305112107/10000000000 : ℝ)|=(5305112107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9761307/50000000 : ℝ)|^4311 ≤ (11735972101599/100000000000000 : ℝ)^3287
        have hw : |(-9761307/50000000 : ℝ)|=(9761307/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414006507/10000000000 : ℝ)|^4311 ≤ (11180000253647/25000000000000 : ℝ)^3287
        have hw : |(5414006507/10000000000 : ℝ)|=(5414006507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s4_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652556219/5000000000 : ℝ)*x 0 + (5414006337/10000000000 : ℝ)*x 1 + (-97613059/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652556219/5000000000 : ℝ)^4311 ≤ (10886007609073/25000000000000 : ℝ)^3287 := by
    have hnat : (2652556219 : ℕ)^4311*25000000000000^3287 ≤ 10886007609073^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652556219 5000000000 10886007609073 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414006337/10000000000 : ℝ)^4311 ≤ (11179999793231/25000000000000 : ℝ)^3287 := by
    have hnat : (5414006337 : ℕ)^4311*25000000000000^3287 ≤ 11179999793231^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414006337 10000000000 11179999793231 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97613059/500000000 : ℝ)^4311 ≤ (2933992591767/25000000000000 : ℝ)^3287 := by
    have hnat : (97613059 : ℕ)^4311*25000000000000^3287 ≤ 2933992591767^3287*500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97613059 500000000 2933992591767 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652556219/5000000000 : ℝ), (5414006337/10000000000 : ℝ), (-97613059/500000000 : ℝ)] ![(10886007609073/25000000000000 : ℝ), (11179999793231/25000000000000 : ℝ), (2933992591767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652556219/5000000000 : ℝ)|^4311 ≤ (10886007609073/25000000000000 : ℝ)^3287
        have hw : |(2652556219/5000000000 : ℝ)|=(2652556219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414006337/10000000000 : ℝ)|^4311 ≤ (11179999793231/25000000000000 : ℝ)^3287
        have hw : |(5414006337/10000000000 : ℝ)|=(5414006337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97613059/500000000 : ℝ)|^4311 ≤ (2933992591767/25000000000000 : ℝ)^3287
        have hw : |(-97613059/500000000 : ℝ)|=(97613059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s4_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162066607/5000000000 : ℝ)*x 0 + (281688163/625000000 : ℝ)*x 1 + (4148237299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162066607/5000000000 : ℝ)^4311 ≤ (33302021888449/100000000000000 : ℝ)^3287 := by
    have hnat : (2162066607 : ℕ)^4311*100000000000000^3287 ≤ 33302021888449^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162066607 5000000000 33302021888449 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281688163/625000000 : ℝ)^4311 ≤ (35161257277459/100000000000000 : ℝ)^3287 := by
    have hnat : (281688163 : ℕ)^4311*100000000000000^3287 ≤ 35161257277459^3287*625000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281688163 625000000 35161257277459 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148237299/10000000000 : ℝ)^4311 ≤ (31536720821979/100000000000000 : ℝ)^3287 := by
    have hnat : (4148237299 : ℕ)^4311*100000000000000^3287 ≤ 31536720821979^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148237299 10000000000 31536720821979 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162066607/5000000000 : ℝ), (281688163/625000000 : ℝ), (4148237299/10000000000 : ℝ)] ![(33302021888449/100000000000000 : ℝ), (35161257277459/100000000000000 : ℝ), (31536720821979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162066607/5000000000 : ℝ)|^4311 ≤ (33302021888449/100000000000000 : ℝ)^3287
        have hw : |(2162066607/5000000000 : ℝ)|=(2162066607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281688163/625000000 : ℝ)|^4311 ≤ (35161257277459/100000000000000 : ℝ)^3287
        have hw : |(281688163/625000000 : ℝ)|=(281688163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148237299/10000000000 : ℝ)|^4311 ≤ (31536720821979/100000000000000 : ℝ)^3287
        have hw : |(4148237299/10000000000 : ℝ)|=(4148237299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5561/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10899/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (4439616592934533/50000000000000000000 : ℝ) := by
    have hpowers : (10899/100000 : ℝ)^2155 ≤ (4439616592934533/50000000000000000000 : ℝ)^512 := by
      have hnat : (10899 : ℕ)^2155*50000000000000000000^512 ≤ 4439616592934533^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10899 100000 4439616592934533 50000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10899/100000 : ℝ)) (X := (4439616592934533/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15001/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (34064564531668303/100000000000000000000 : ℝ) := by
    have hpowers : (15001/100000 : ℝ)^2155 ≤ (34064564531668303/100000000000000000000 : ℝ)^512 := by
      have hnat : (15001 : ℕ)^2155*100000000000000000000^512 ≤ 34064564531668303^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15001 100000 34064564531668303 100000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15001/100000 : ℝ)) (X := (34064564531668303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004439616592934533/25000000000000000000 : ℝ) ≤ (500021094476399/500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (25004439616592934533/25000000000000000000 : ℝ)^512 ≤ (500021094476399/500000000000000 : ℝ)^2155 := by
      have hnat : (25004439616592934533 : ℕ)^512*500000000000000^2155 ≤ 500021094476399^2155*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004439616592934533 25000000000000000000 500021094476399 500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500021094476399/500000000000000 : ℝ)) (X := (25004439616592934533/25000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042943797717537369/100000000000000000000 : ℝ) ≤ (10001020121852927/10000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (100042943797717537369/100000000000000000000 : ℝ)^512 ≤ (10001020121852927/10000000000000000 : ℝ)^2155 := by
      have hnat : (100042943797717537369 : ℕ)^512*10000000000000000^2155 ≤ 10001020121852927^2155*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042943797717537369 100000000000000000000 10001020121852927 10000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001020121852927/10000000000000000 : ℝ)) (X := (100042943797717537369/100000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034064564531668303/50000000000000000000 : ℝ) ≤ (5000809177088937/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (50034064564531668303/50000000000000000000 : ℝ)^512 ≤ (5000809177088937/5000000000000000 : ℝ)^2155 := by
      have hnat : (50034064564531668303 : ℕ)^512*5000000000000000^2155 ≤ 5000809177088937^2155*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034064564531668303 50000000000000000000 5000809177088937 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000809177088937/5000000000000000 : ℝ)) (X := (50034064564531668303/50000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4439616592934533/50000000000000000000 : ℝ) ≤ ((2929192165901755661/2930000000000000000 : ℝ)+2*(598232324947/410200000000000 : ℝ)*(10899/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (2929192165901755661/2930000000000000000 : ℝ)+2*(598232324947/410200000000000 : ℝ)*(10899/100000 : ℝ)=(500021094476399/500000000000000 : ℝ) by norm_num, show 1+2*(4439616592934533/50000000000000000000 : ℝ)=(25004439616592934533/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34064564531668303/100000000000000000000 : ℝ)+(4439616592934533/50000000000000000000 : ℝ) ≤ ((2929192165901755661/2930000000000000000 : ℝ)+(598232324947/410200000000000 : ℝ)*((15001/100000 : ℝ)+(10899/100000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (2929192165901755661/2930000000000000000 : ℝ)+(598232324947/410200000000000 : ℝ)*((15001/100000 : ℝ)+(10899/100000 : ℝ))=(10001020121852927/10000000000000000 : ℝ) by norm_num, show 1+(34064564531668303/100000000000000000000 : ℝ)+(4439616592934533/50000000000000000000 : ℝ)=(100042943797717537369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34064564531668303/100000000000000000000 : ℝ) ≤ ((2929192165901755661/2930000000000000000 : ℝ)+2*(598232324947/410200000000000 : ℝ)*(15001/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (2929192165901755661/2930000000000000000 : ℝ)+2*(598232324947/410200000000000 : ℝ)*(15001/100000 : ℝ)=(5000809177088937/5000000000000000 : ℝ) by norm_num, show 1+2*(34064564531668303/100000000000000000000 : ℝ)=(50034064564531668303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2929192165901755661/2930000000000000000 : ℝ)*(X 1 0+X 2 0)+(598232324947/410200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (10899/100000 : ℝ)) (hi := (15001/100000 : ℝ)) (c := (2929192165901755661/2930000000000000000 : ℝ)) (alpha := (598232324947/410200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2929192165901755661/2930000000000000000 : ℝ)*(X 0 1+X 2 1)+(598232324947/410200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (10899/100000 : ℝ)) (hi := (15001/100000 : ℝ)) (c := (2929192165901755661/2930000000000000000 : ℝ)) (alpha := (598232324947/410200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2929192165901755661/2930000000000000000 : ℝ)*(X 0 2+X 1 2)+(598232324947/410200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (10899/100000 : ℝ)) (hi := (15001/100000 : ℝ)) (c := (2929192165901755661/2930000000000000000 : ℝ)) (alpha := (598232324947/410200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1017970627/5000000000 : ℝ)*X 0 0+(5414642817/10000000000 : ℝ)*X 0 1+(1048532951/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349455701/10000000000 : ℝ)*X 1 0+(-2123602789/10000000000 : ℝ)*X 1 1+(5242664727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349455699/10000000000 : ℝ)*X 2 0+(5242664747/10000000000 : ℝ)*X 2 1+(-424720553/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324105473/10000000000 : ℝ)*X 0 0+(2073450101/5000000000 : ℝ)*X 0 1+(2254170427/5000000000 : ℝ)*X 0 2+(4324105473/10000000000 : ℝ)*X 1 0+(2073450101/5000000000 : ℝ)*X 1 1+(2254170427/5000000000 : ℝ)*X 1 2+(4324105473/10000000000 : ℝ)*X 2 0+(2073450101/5000000000 : ℝ)*X 2 1+(2254170427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-127247149/625000000 : ℝ)*X 0 0+(81926529/156250000 : ℝ)*X 0 1+(676750793/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305112107/10000000000 : ℝ)*X 1 0+(-9761307/50000000 : ℝ)*X 1 1+(5414006507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652556219/5000000000 : ℝ)*X 2 0+(5414006337/10000000000 : ℝ)*X 2 1+(-97613059/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162066607/5000000000 : ℝ)*X 0 0+(281688163/625000000 : ℝ)*X 0 1+(4148237299/10000000000 : ℝ)*X 0 2+(2162066607/5000000000 : ℝ)*X 1 0+(281688163/625000000 : ℝ)*X 1 1+(4148237299/10000000000 : ℝ)*X 1 2+(2162066607/5000000000 : ℝ)*X 2 0+(281688163/625000000 : ℝ)*X 2 1+(4148237299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180865241157460951641521781/16023437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2123838833/100000000000000 : ℝ)*(base19) + (1991100779/100000000000000 : ℝ)*(base23) + (34922339/50000000000000 : ℝ)*(lower2) + (130170621/50000000000000 : ℝ)*(upper3) + (47985453/25000000000000 : ℝ)*(upper5) + (134086390023401/3125000000000 : ℝ)*(major0) + (134086390023401/3125000000000 : ℝ)*(major1) + (134086390023401/3125000000000 : ℝ)*(major2) + (90855290972139/1562500000000 : ℝ)*(sp0) + (1162955864539663/20000000000000 : ℝ)*(sp1) + (5814779455436369/100000000000000 : ℝ)*(sp2) + (1383362856287947/50000000000000 : ℝ)*(sp3) + (10706080063/25000000000000 : ℝ)*(sp4) + (10713066589/50000000000000 : ℝ)*(sp7) + (172921696169317/6250000000000 : ℝ)*(f.failure) + (1453695361634287/25000000000000 : ℝ)*(f.sum) + (28026554893721/5127500000000000000000000000 : ℝ)*base65 + (272283076583286427/64093750000000000000000000000000 : ℝ)*base67 + (669950188910776073/64093750000000000000000000000000 : ℝ)*base70 + (256822828849932323/64093750000000000000000000000000 : ℝ)*base72 + (1422133605317/10255000000000000000000000000 : ℝ)*base73 + (1571906655213494823/64093750000000000000000000000000 : ℝ)*base76 + (308038421378557323/64093750000000000000000000000000 : ℝ)*base78 + (1313817259693244823/64093750000000000000000000000000 : ℝ)*base80 + (15301075724363/10255000000000000000000000000 : ℝ)*base82 + (801877/312500000000000000000 : ℝ)*base89 + (801877/312500000000000000000 : ℝ)*base91 + (801877/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (448493802576151553842529331/73250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (499811073/100000000000000 : ℝ)*(base19) + (580565003/50000000000000 : ℝ)*(base23) + (260113799/100000000000000 : ℝ)*(upper3) + (18866441/25000000000000 : ℝ)*(lower4) + (52845949/100000000000000 : ℝ)*(upper5) + (2161303410953719/50000000000000 : ℝ)*(major0) + (2161303410953719/50000000000000 : ℝ)*(major1) + (2161303410953719/50000000000000 : ℝ)*(major2) + (3769282347/100000000000000 : ℝ)*(sp1) + (1107136917/5000000000000 : ℝ)*(sp2) + (2928966948914053/50000000000000 : ℝ)*(sp4) + (1171585925746937/20000000000000 : ℝ)*(sp5) + (73223882424497/1250000000000 : ℝ)*(sp6) + (21775621421047/781250000000 : ℝ)*(sp7) + (21775621421047/781250000000 : ℝ)*(f.failure) + (2928966948914053/50000000000000 : ℝ)*(f.sum) + (11226774594293/10255000000000000000000000000 : ℝ)*base65 + (14654517976816577187/1025500000000000000000000000000000 : ℝ)*base68 + (14839256452808577187/1025500000000000000000000000000000 : ℝ)*base70 + (3871822854617577187/1025500000000000000000000000000000 : ℝ)*base72 + (613735228459/5127500000000000000000000000 : ℝ)*base73 + (26921456562858577187/1025500000000000000000000000000000 : ℝ)*base76 + (6439831754066577187/1025500000000000000000000000000000 : ℝ)*base78 + (25401715279098577187/1025500000000000000000000000000000 : ℝ)*base80 + (49312355937473/10255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (191257/39062500000000000000 : ℝ)*base89 + (191257/39062500000000000000 : ℝ)*base91 + (191257/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1351_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1351_s5_0 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018089617/5000000000 : ℝ)*x 0 + (216504049/400000000 : ℝ)*x 1 + (1048909901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018089617/5000000000 : ℝ)^4311 ≤ (3100496712663/25000000000000 : ℝ)^3287 := by
    have hnat : (1018089617 : ℕ)^4311*25000000000000^3287 ≤ 3100496712663^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018089617 5000000000 3100496712663 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216504049/400000000 : ℝ)^4311 ≤ (22352388884157/50000000000000 : ℝ)^3287 := by
    have hnat : (216504049 : ℕ)^4311*50000000000000^3287 ≤ 22352388884157^3287*400000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216504049 400000000 22352388884157 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048909901/2000000000 : ℝ)^4311 ≤ (1715729414303/4000000000000 : ℝ)^3287 := by
    have hnat : (1048909901 : ℕ)^4311*4000000000000^3287 ≤ 1715729414303^3287*2000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048909901 2000000000 1715729414303 4000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018089617/5000000000 : ℝ), (216504049/400000000 : ℝ), (1048909901/2000000000 : ℝ)] ![(3100496712663/25000000000000 : ℝ), (22352388884157/50000000000000 : ℝ), (1715729414303/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018089617/5000000000 : ℝ)|^4311 ≤ (3100496712663/25000000000000 : ℝ)^3287
        have hw : |(-1018089617/5000000000 : ℝ)|=(1018089617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216504049/400000000 : ℝ)|^4311 ≤ (22352388884157/50000000000000 : ℝ)^3287
        have hw : |(216504049/400000000 : ℝ)|=(216504049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048909901/2000000000 : ℝ)|^4311 ≤ (1715729414303/4000000000000 : ℝ)^3287
        have hw : |(1048909901/2000000000 : ℝ)|=(1048909901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s5_1 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337233199/2500000000 : ℝ)*x 0 + (-2121801991/10000000000 : ℝ)*x 1 + (5244549561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337233199/2500000000 : ℝ)^4311 ≤ (8803272109383/20000000000000 : ℝ)^3287 := by
    have hnat : (1337233199 : ℕ)^4311*20000000000000^3287 ≤ 8803272109383^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337233199 2500000000 8803272109383 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121801991/10000000000 : ℝ)^4311 ≤ (6545201742841/50000000000000 : ℝ)^3287 := by
    have hnat : (2121801991 : ℕ)^4311*50000000000000^3287 ≤ 6545201742841^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121801991 10000000000 6545201742841 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244549561/10000000000 : ℝ)^4311 ≤ (2144661797913/5000000000000 : ℝ)^3287 := by
    have hnat : (5244549561 : ℕ)^4311*5000000000000^3287 ≤ 2144661797913^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244549561 10000000000 2144661797913 5000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337233199/2500000000 : ℝ), (-2121801991/10000000000 : ℝ), (5244549561/10000000000 : ℝ)] ![(8803272109383/20000000000000 : ℝ), (6545201742841/50000000000000 : ℝ), (2144661797913/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337233199/2500000000 : ℝ)|^4311 ≤ (8803272109383/20000000000000 : ℝ)^3287
        have hw : |(1337233199/2500000000 : ℝ)|=(1337233199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121801991/10000000000 : ℝ)|^4311 ≤ (6545201742841/50000000000000 : ℝ)^3287
        have hw : |(-2121801991/10000000000 : ℝ)|=(2121801991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244549561/10000000000 : ℝ)|^4311 ≤ (2144661797913/5000000000000 : ℝ)^3287
        have hw : |(5244549561/10000000000 : ℝ)|=(5244549561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s5_2 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348932523/10000000000 : ℝ)*x 0 + (2622274829/5000000000 : ℝ)*x 1 + (-1060901113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348932523/10000000000 : ℝ)^4311 ≤ (44016357600541/100000000000000 : ℝ)^3287 := by
    have hnat : (5348932523 : ℕ)^4311*100000000000000^3287 ≤ 44016357600541^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348932523 10000000000 44016357600541 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622274829/5000000000 : ℝ)^4311 ≤ (10723309249683/25000000000000 : ℝ)^3287 := by
    have hnat : (2622274829 : ℕ)^4311*25000000000000^3287 ≤ 10723309249683^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622274829 5000000000 10723309249683 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060901113/5000000000 : ℝ)^4311 ≤ (13090405387173/100000000000000 : ℝ)^3287 := by
    have hnat : (1060901113 : ℕ)^4311*100000000000000^3287 ≤ 13090405387173^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060901113 5000000000 13090405387173 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348932523/10000000000 : ℝ), (2622274829/5000000000 : ℝ), (-1060901113/5000000000 : ℝ)] ![(44016357600541/100000000000000 : ℝ), (10723309249683/25000000000000 : ℝ), (13090405387173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348932523/10000000000 : ℝ)|^4311 ≤ (44016357600541/100000000000000 : ℝ)^3287
        have hw : |(5348932523/10000000000 : ℝ)|=(5348932523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622274829/5000000000 : ℝ)|^4311 ≤ (10723309249683/25000000000000 : ℝ)^3287
        have hw : |(2622274829/5000000000 : ℝ)|=(2622274829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1060901113/5000000000 : ℝ)|^4311 ≤ (13090405387173/100000000000000 : ℝ)^3287
        have hw : |(-1060901113/5000000000 : ℝ)|=(1060901113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s5_3 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4324246417/10000000000 : ℝ)*x 0 + (1037752209/2500000000 : ℝ)*x 1 + (1126049367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324246417/10000000000 : ℝ)^4311 ≤ (16651582659199/50000000000000 : ℝ)^3287 := by
    have hnat : (4324246417 : ℕ)^4311*50000000000000^3287 ≤ 16651582659199^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324246417 10000000000 16651582659199 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037752209/2500000000 : ℝ)^4311 ≤ (1578217910923/5000000000000 : ℝ)^3287 := by
    have hnat : (1037752209 : ℕ)^4311*5000000000000^3287 ≤ 1578217910923^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037752209 2500000000 1578217910923 5000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126049367/2500000000 : ℝ)^4311 ≤ (8783119112953/25000000000000 : ℝ)^3287 := by
    have hnat : (1126049367 : ℕ)^4311*25000000000000^3287 ≤ 8783119112953^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126049367 2500000000 8783119112953 25000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324246417/10000000000 : ℝ), (1037752209/2500000000 : ℝ), (1126049367/2500000000 : ℝ)] ![(16651582659199/50000000000000 : ℝ), (1578217910923/5000000000000 : ℝ), (8783119112953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324246417/10000000000 : ℝ)|^4311 ≤ (16651582659199/50000000000000 : ℝ)^3287
        have hw : |(4324246417/10000000000 : ℝ)|=(4324246417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037752209/2500000000 : ℝ)|^4311 ≤ (1578217910923/5000000000000 : ℝ)^3287
        have hw : |(1037752209/2500000000 : ℝ)|=(1037752209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126049367/2500000000 : ℝ)|^4311 ≤ (8783119112953/25000000000000 : ℝ)^3287
        have hw : |(1126049367/2500000000 : ℝ)|=(1126049367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s5_4 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036191299/10000000000 : ℝ)*x 0 + (81955533/156250000 : ℝ)*x 1 + (1352998403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036191299/10000000000 : ℝ)^4311 ≤ (6201041614703/50000000000000 : ℝ)^3287 := by
    have hnat : (2036191299 : ℕ)^4311*50000000000000^3287 ≤ 6201041614703^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036191299 10000000000 6201041614703 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81955533/156250000 : ℝ)^4311 ≤ (5362465100553/12500000000000 : ℝ)^3287 := by
    have hnat : (81955533 : ℕ)^4311*12500000000000^3287 ≤ 5362465100553^3287*156250000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81955533 156250000 5362465100553 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352998403/2500000000 : ℝ)^4311 ≤ (44698195953023/100000000000000 : ℝ)^3287 := by
    have hnat : (1352998403 : ℕ)^4311*100000000000000^3287 ≤ 44698195953023^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352998403 2500000000 44698195953023 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036191299/10000000000 : ℝ), (81955533/156250000 : ℝ), (1352998403/2500000000 : ℝ)] ![(6201041614703/50000000000000 : ℝ), (5362465100553/12500000000000 : ℝ), (44698195953023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036191299/10000000000 : ℝ)|^4311 ≤ (6201041614703/50000000000000 : ℝ)^3287
        have hw : |(-2036191299/10000000000 : ℝ)|=(2036191299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81955533/156250000 : ℝ)|^4311 ≤ (5362465100553/12500000000000 : ℝ)^3287
        have hw : |(81955533/156250000 : ℝ)|=(81955533/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352998403/2500000000 : ℝ)|^4311 ≤ (44698195953023/100000000000000 : ℝ)^3287
        have hw : |(1352998403/2500000000 : ℝ)|=(1352998403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s5_5 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331600119/625000000 : ℝ)*x 0 + (-78174317/400000000 : ℝ)*x 1 + (5411993619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331600119/625000000 : ℝ)^4311 ≤ (1088732489827/2500000000000 : ℝ)^3287 := by
    have hnat : (331600119 : ℕ)^4311*2500000000000^3287 ≤ 1088732489827^3287*625000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331600119 625000000 1088732489827 2500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78174317/400000000 : ℝ)^4311 ≤ (73453152227/625000000000 : ℝ)^3287 := by
    have hnat : (78174317 : ℕ)^4311*625000000000^3287 ≤ 73453152227^3287*400000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78174317 400000000 73453152227 625000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411993619/10000000000 : ℝ)^4311 ≤ (44698196028847/100000000000000 : ℝ)^3287 := by
    have hnat : (5411993619 : ℕ)^4311*100000000000000^3287 ≤ 44698196028847^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411993619 10000000000 44698196028847 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331600119/625000000 : ℝ), (-78174317/400000000 : ℝ), (5411993619/10000000000 : ℝ)] ![(1088732489827/2500000000000 : ℝ), (73453152227/625000000000 : ℝ), (44698196028847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331600119/625000000 : ℝ)|^4311 ≤ (1088732489827/2500000000000 : ℝ)^3287
        have hw : |(331600119/625000000 : ℝ)|=(331600119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78174317/400000000 : ℝ)|^4311 ≤ (73453152227/625000000000 : ℝ)^3287
        have hw : |(-78174317/400000000 : ℝ)|=(78174317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411993619/10000000000 : ℝ)|^4311 ≤ (44698196028847/100000000000000 : ℝ)^3287
        have hw : |(5411993619/10000000000 : ℝ)|=(5411993619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s5_6 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305601899/10000000000 : ℝ)*x 0 + (5411993621/10000000000 : ℝ)*x 1 + (-1954357931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305601899/10000000000 : ℝ)^4311 ≤ (21774649769627/50000000000000 : ℝ)^3287 := by
    have hnat : (5305601899 : ℕ)^4311*50000000000000^3287 ≤ 21774649769627^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305601899 10000000000 21774649769627 50000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411993621/10000000000 : ℝ)^4311 ≤ (44698196050511/100000000000000 : ℝ)^3287 := by
    have hnat : (5411993621 : ℕ)^4311*100000000000000^3287 ≤ 44698196050511^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411993621 10000000000 44698196050511 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954357931/10000000000 : ℝ)^4311 ≤ (11752504403641/100000000000000 : ℝ)^3287 := by
    have hnat : (1954357931 : ℕ)^4311*100000000000000^3287 ≤ 11752504403641^3287*10000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954357931 10000000000 11752504403641 100000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305601899/10000000000 : ℝ), (5411993621/10000000000 : ℝ), (-1954357931/10000000000 : ℝ)] ![(21774649769627/50000000000000 : ℝ), (44698196050511/100000000000000 : ℝ), (11752504403641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305601899/10000000000 : ℝ)|^4311 ≤ (21774649769627/50000000000000 : ℝ)^3287
        have hw : |(5305601899/10000000000 : ℝ)|=(5305601899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411993621/10000000000 : ℝ)|^4311 ≤ (44698196050511/100000000000000 : ℝ)^3287
        have hw : |(5411993621/10000000000 : ℝ)|=(5411993621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1954357931/10000000000 : ℝ)|^4311 ≤ (11752504403641/100000000000000 : ℝ)^3287
        have hw : |(-1954357931/10000000000 : ℝ)|=(1954357931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1351_s5_7 (p : ℝ) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081068067/2500000000 : ℝ)*x 0 + (225146347/500000000 : ℝ)*x 1 + (2076142899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081068067/2500000000 : ℝ)^4311 ≤ (6660685286599/20000000000000 : ℝ)^3287 := by
    have hnat : (1081068067 : ℕ)^4311*20000000000000^3287 ≤ 6660685286599^3287*2500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081068067 2500000000 6660685286599 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225146347/500000000 : ℝ)^4311 ≤ (7023895940049/20000000000000 : ℝ)^3287 := by
    have hnat : (225146347 : ℕ)^4311*20000000000000^3287 ≤ 7023895940049^3287*500000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225146347 500000000 7023895940049 20000000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076142899/5000000000 : ℝ)^4311 ≤ (3947136730959/12500000000000 : ℝ)^3287 := by
    have hnat : (2076142899 : ℕ)^4311*12500000000000^3287 ≤ 3947136730959^3287*5000000000^4311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076142899 5000000000 3947136730959 12500000000000 4311 3287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4311/1024 : ℝ)) 4311 3287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081068067/2500000000 : ℝ), (225146347/500000000 : ℝ), (2076142899/5000000000 : ℝ)] ![(6660685286599/20000000000000 : ℝ), (7023895940049/20000000000000 : ℝ), (3947136730959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081068067/2500000000 : ℝ)|^4311 ≤ (6660685286599/20000000000000 : ℝ)^3287
        have hw : |(1081068067/2500000000 : ℝ)|=(1081068067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225146347/500000000 : ℝ)|^4311 ≤ (7023895940049/20000000000000 : ℝ)^3287
        have hw : |(225146347/500000000 : ℝ)|=(225146347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2076142899/5000000000 : ℝ)|^4311 ≤ (3947136730959/12500000000000 : ℝ)^3287
        have hw : |(2076142899/5000000000 : ℝ)|=(2076142899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1351_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11163/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (92/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5561/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5561/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5561/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5561/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5561/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5561/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5561/50000 : ℝ) ^ (2155/512 : ℝ) ≤ (604336336940579/6250000000000000000 : ℝ) := by
    have hpowers : (5561/50000 : ℝ)^2155 ≤ (604336336940579/6250000000000000000 : ℝ)^512 := by
      have hnat : (5561 : ℕ)^2155*6250000000000000000^512 ≤ 604336336940579^512*50000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5561 50000 604336336940579 6250000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5561/50000 : ℝ)) (X := (604336336940579/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (2155/512 : ℝ) ≤ (31847031407726563/100000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^2155 ≤ (31847031407726563/100000000000000000000 : ℝ)^512 := by
      have hnat : (14763 : ℕ)^2155*100000000000000000000^512 ≤ 31847031407726563^512*100000^2155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 31847031407726563 100000000000000000000 2155 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (31847031407726563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125604336336940579/3125000000000000000 : ℝ) ≤ (5000229715004329/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (3125604336336940579/3125000000000000000 : ℝ)^512 ≤ (5000229715004329/5000000000000000 : ℝ)^2155 := by
      have hnat : (3125604336336940579 : ℕ)^512*5000000000000000^2155 ≤ 5000229715004329^2155*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125604336336940579 3125000000000000000 5000229715004329 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000229715004329/5000000000000000 : ℝ)) (X := (3125604336336940579/3125000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041516412798775827/100000000000000000000 : ℝ) ≤ (2500246554989159/2500000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (100041516412798775827/100000000000000000000 : ℝ)^512 ≤ (2500246554989159/2500000000000000 : ℝ)^2155 := by
      have hnat : (100041516412798775827 : ℕ)^512*2500000000000000^2155 ≤ 2500246554989159^2155*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041516412798775827 100000000000000000000 2500246554989159 2500000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500246554989159/2500000000000000 : ℝ)) (X := (100041516412798775827/100000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031847031407726563/50000000000000000000 : ℝ) ≤ (5000756504952307/5000000000000000 : ℝ) ^ (2155/512 : ℝ) := by
    have hpowers : (50031847031407726563/50000000000000000000 : ℝ)^512 ≤ (5000756504952307/5000000000000000 : ℝ)^2155 := by
      have hnat : (50031847031407726563 : ℕ)^512*5000000000000000^2155 ≤ 5000756504952307^2155*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031847031407726563 50000000000000000000 5000756504952307 5000000000000000 512 2155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000756504952307/5000000000000000 : ℝ)) (X := (50031847031407726563/50000000000000000000 : ℝ)) (by norm_num) 2155 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(604336336940579/6250000000000000000 : ℝ) ≤ ((18199977434529350573/18205000000000000000 : ℝ)+2*(263394973989/182050000000000 : ℝ)*(5561/50000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (18199977434529350573/18205000000000000000 : ℝ)+2*(263394973989/182050000000000 : ℝ)*(5561/50000 : ℝ)=(5000229715004329/5000000000000000 : ℝ) by norm_num, show 1+2*(604336336940579/6250000000000000000 : ℝ)=(3125604336336940579/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31847031407726563/100000000000000000000 : ℝ)+(604336336940579/6250000000000000000 : ℝ) ≤ ((18199977434529350573/18205000000000000000 : ℝ)+(263394973989/182050000000000 : ℝ)*((14763/100000 : ℝ)+(5561/50000 : ℝ)))^(2155/512 : ℝ) := by
    rw [show (18199977434529350573/18205000000000000000 : ℝ)+(263394973989/182050000000000 : ℝ)*((14763/100000 : ℝ)+(5561/50000 : ℝ))=(2500246554989159/2500000000000000 : ℝ) by norm_num, show 1+(31847031407726563/100000000000000000000 : ℝ)+(604336336940579/6250000000000000000 : ℝ)=(100041516412798775827/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31847031407726563/100000000000000000000 : ℝ) ≤ ((18199977434529350573/18205000000000000000 : ℝ)+2*(263394973989/182050000000000 : ℝ)*(14763/100000 : ℝ))^(2155/512 : ℝ) := by
    rw [show (18199977434529350573/18205000000000000000 : ℝ)+2*(263394973989/182050000000000 : ℝ)*(14763/100000 : ℝ)=(5000756504952307/5000000000000000 : ℝ) by norm_num, show 1+2*(31847031407726563/100000000000000000000 : ℝ)=(50031847031407726563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18199977434529350573/18205000000000000000 : ℝ)*(X 1 0+X 2 0)+(263394973989/182050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (18199977434529350573/18205000000000000000 : ℝ)) (alpha := (263394973989/182050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18199977434529350573/18205000000000000000 : ℝ)*(X 0 1+X 2 1)+(263394973989/182050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (18199977434529350573/18205000000000000000 : ℝ)) (alpha := (263394973989/182050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18199977434529350573/18205000000000000000 : ℝ)*(X 0 2+X 1 2)+(263394973989/182050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2155/512 : ℝ)) (lo := (5561/50000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (18199977434529350573/18205000000000000000 : ℝ)) (alpha := (263394973989/182050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1018089617/5000000000 : ℝ)*X 0 0+(216504049/400000000 : ℝ)*X 0 1+(1048909901/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337233199/2500000000 : ℝ)*X 1 0+(-2121801991/10000000000 : ℝ)*X 1 1+(5244549561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348932523/10000000000 : ℝ)*X 2 0+(2622274829/5000000000 : ℝ)*X 2 1+(-1060901113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324246417/10000000000 : ℝ)*X 0 0+(1037752209/2500000000 : ℝ)*X 0 1+(1126049367/2500000000 : ℝ)*X 0 2+(4324246417/10000000000 : ℝ)*X 1 0+(1037752209/2500000000 : ℝ)*X 1 1+(1126049367/2500000000 : ℝ)*X 1 2+(4324246417/10000000000 : ℝ)*X 2 0+(1037752209/2500000000 : ℝ)*X 2 1+(1126049367/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2036191299/10000000000 : ℝ)*X 0 0+(81955533/156250000 : ℝ)*X 0 1+(1352998403/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331600119/625000000 : ℝ)*X 1 0+(-78174317/400000000 : ℝ)*X 1 1+(5411993619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305601899/10000000000 : ℝ)*X 2 0+(5411993621/10000000000 : ℝ)*X 2 1+(-1954357931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081068067/2500000000 : ℝ)*X 0 0+(225146347/500000000 : ℝ)*X 0 1+(2076142899/5000000000 : ℝ)*X 0 2+(1081068067/2500000000 : ℝ)*X 1 0+(225146347/500000000 : ℝ)*X 1 1+(2076142899/5000000000 : ℝ)*X 1 2+(1081068067/2500000000 : ℝ)*X 2 0+(225146347/500000000 : ℝ)*X 2 1+(2076142899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1351_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70781321564381375428027413/16550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67748001/10000000000000 : ℝ)*(base19) + (503836407/100000000000000 : ℝ)*(base23) + (98575703/100000000000000 : ℝ)*(upper2) + (248492581/100000000000000 : ℝ)*(upper3) + (7251453/25000000000000 : ℝ)*(upper4) + (878193458139297/20000000000000 : ℝ)*(major0) + (878193458139297/20000000000000 : ℝ)*(major1) + (878193458139297/20000000000000 : ℝ)*(major2) + (1487642171325787/25000000000000 : ℝ)*(sp0) + (1487643599547103/25000000000000 : ℝ)*(sp1) + (2975287285916007/50000000000000 : ℝ)*(sp2) + (283135274468903/10000000000000 : ℝ)*(sp3) + (3195182637/50000000000000 : ℝ)*(sp4) + (6618474947/100000000000000 : ℝ)*(sp7) + (2831359363163977/100000000000000 : ℝ)*(f.failure) + (5950575075668421/100000000000000 : ℝ)*(f.sum) + (7238700186499/1820500000000000000000000000 : ℝ)*base65 + (459195944257267181/364100000000000000000000000000000 : ℝ)*base67 + (217646267399332819/364100000000000000000000000000000 : ℝ)*base70 + (449900226483732819/364100000000000000000000000000000 : ℝ)*base72 + (2559437687489/1820500000000000000000000000 : ℝ)*base73 + (329626724774267181/364100000000000000000000000000000 : ℝ)*base75 + (3888180768300732819/364100000000000000000000000000000 : ℝ)*base78 + (630514658101132819/364100000000000000000000000000000 : ℝ)*base80 + (5623338439351/910250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5225337/5000000000000000000000 : ℝ)*base89 + (5225337/5000000000000000000000 : ℝ)*base91 + (5225337/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2130665732606414516317768497/910250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45272079/10000000000000 : ℝ)*(base19) + (56169343/12500000000000 : ℝ)*(base23) + (874177/100000000000000 : ℝ)*(upper2) + (14484113/25000000000000 : ℝ)*(upper3) + (3083263/6250000000000 : ℝ)*(upper5) + (4422851404184137/100000000000000 : ℝ)*(major0) + (4422851404184137/100000000000000 : ℝ)*(major1) + (4422851404184137/100000000000000 : ℝ)*(major2) + (3678071/40000000000 : ℝ)*(sp1) + (9272968229/100000000000000 : ℝ)*(sp2) + (5993784028591093/100000000000000 : ℝ)*(sp4) + (5993774380692803/100000000000000 : ℝ)*(sp5) + (5993774306268119/100000000000000 : ℝ)*(sp6) + (2851918701752247/100000000000000 : ℝ)*(sp7) + (2851918701752247/100000000000000 : ℝ)*(f.failure) + (5993784028591093/100000000000000 : ℝ)*(f.sum) + (24440384113241/18205000000000000000000000000 : ℝ)*base65 + (6270149647250239499/1820500000000000000000000000000000 : ℝ)*base68 + (9579619573716760501/1820500000000000000000000000000000 : ℝ)*base69 + (7763512283653760501/1820500000000000000000000000000000 : ℝ)*base71 + (12122307364461/18205000000000000000000000000 : ℝ)*base73 + (2984021654723739499/1820500000000000000000000000000000 : ℝ)*base76 + (1598966430715760501/1820500000000000000000000000000000 : ℝ)*base77 + (34918735372367260501/1820500000000000000000000000000000 : ℝ)*base79 + (65951021435571/18205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (27907207/5000000000000000000000 : ℝ)*base89 + (27907207/5000000000000000000000 : ℝ)*base91 + (27907207/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1351_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5561/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1351_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1351_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1351_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1351_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1351_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2155/512 : ℝ) ≤ p) (hpb : p ≤ (4311/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77541681/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (991/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1351_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
