-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:11:22.720552+00:00
-- url     : https://prove2.me/submissions/f1caae83-ef2d-407c-bfc2-3b53fea694cd

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
theorem support_rectangle_w1221_s3_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-531661117/2500000000 : ℝ)*x 0 + (542153527/1000000000 : ℝ)*x 1 + (2619481671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531661117/2500000000 : ℝ)^4207 ≤ (12924335786121/100000000000000 : ℝ)^3183 := by
    have hnat : (531661117 : ℕ)^4207*100000000000000^3183 ≤ 12924335786121^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531661117 2500000000 12924335786121 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542153527/1000000000 : ℝ)^4207 ≤ (44523265878159/100000000000000 : ℝ)^3183 := by
    have hnat : (542153527 : ℕ)^4207*100000000000000^3183 ≤ 44523265878159^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542153527 1000000000 44523265878159 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619481671/5000000000 : ℝ)^4207 ≤ (42552398327051/100000000000000 : ℝ)^3183 := by
    have hnat : (2619481671 : ℕ)^4207*100000000000000^3183 ≤ 42552398327051^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619481671 5000000000 42552398327051 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531661117/2500000000 : ℝ), (542153527/1000000000 : ℝ), (2619481671/5000000000 : ℝ)] ![(12924335786121/100000000000000 : ℝ), (44523265878159/100000000000000 : ℝ), (42552398327051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531661117/2500000000 : ℝ)|^4207 ≤ (12924335786121/100000000000000 : ℝ)^3183
        have hw : |(-531661117/2500000000 : ℝ)|=(531661117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542153527/1000000000 : ℝ)|^4207 ≤ (44523265878159/100000000000000 : ℝ)^3183
        have hw : |(542153527/1000000000 : ℝ)|=(542153527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619481671/5000000000 : ℝ)|^4207 ≤ (42552398327051/100000000000000 : ℝ)^3183
        have hw : |(2619481671/5000000000 : ℝ)|=(2619481671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s3_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351958671/10000000000 : ℝ)*x 0 + (-110990903/500000000 : ℝ)*x 1 + (2619481777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351958671/10000000000 : ℝ)^4207 ≤ (21884813121407/50000000000000 : ℝ)^3183 := by
    have hnat : (5351958671 : ℕ)^4207*50000000000000^3183 ≤ 21884813121407^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351958671 10000000000 21884813121407 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110990903/500000000 : ℝ)^4207 ≤ (1709746642607/12500000000000 : ℝ)^3183 := by
    have hnat : (110990903 : ℕ)^4207*12500000000000^3183 ≤ 1709746642607^3183*500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110990903 500000000 1709746642607 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619481777/5000000000 : ℝ)^4207 ≤ (5319050075367/12500000000000 : ℝ)^3183 := by
    have hnat : (2619481777 : ℕ)^4207*12500000000000^3183 ≤ 5319050075367^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619481777 5000000000 5319050075367 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351958671/10000000000 : ℝ), (-110990903/500000000 : ℝ), (2619481777/5000000000 : ℝ)] ![(21884813121407/50000000000000 : ℝ), (1709746642607/12500000000000 : ℝ), (5319050075367/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351958671/10000000000 : ℝ)|^4207 ≤ (21884813121407/50000000000000 : ℝ)^3183
        have hw : |(5351958671/10000000000 : ℝ)|=(5351958671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110990903/500000000 : ℝ)|^4207 ≤ (1709746642607/12500000000000 : ℝ)^3183
        have hw : |(-110990903/500000000 : ℝ)|=(110990903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619481777/5000000000 : ℝ)|^4207 ≤ (5319050075367/12500000000000 : ℝ)^3183
        have hw : |(2619481777/5000000000 : ℝ)|=(2619481777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s3_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351958533/10000000000 : ℝ)*x 0 + (1047792789/2000000000 : ℝ)*x 1 + (-8671163/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351958533/10000000000 : ℝ)^4207 ≤ (1367800773473/3125000000000 : ℝ)^3183 := by
    have hnat : (5351958533 : ℕ)^4207*3125000000000^3183 ≤ 1367800773473^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351958533 10000000000 1367800773473 3125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047792789/2000000000 : ℝ)^4207 ≤ (21276202400221/50000000000000 : ℝ)^3183 := by
    have hnat : (1047792789 : ℕ)^4207*50000000000000^3183 ≤ 21276202400221^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047792789 2000000000 21276202400221 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8671163/39062500 : ℝ)^4207 ≤ (13677970437033/100000000000000 : ℝ)^3183 := by
    have hnat : (8671163 : ℕ)^4207*100000000000000^3183 ≤ 13677970437033^3183*39062500^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8671163 39062500 13677970437033 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351958533/10000000000 : ℝ), (1047792789/2000000000 : ℝ), (-8671163/39062500 : ℝ)] ![(1367800773473/3125000000000 : ℝ), (21276202400221/50000000000000 : ℝ), (13677970437033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351958533/10000000000 : ℝ)|^4207 ≤ (1367800773473/3125000000000 : ℝ)^3183
        have hw : |(5351958533/10000000000 : ℝ)|=(5351958533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047792789/2000000000 : ℝ)|^4207 ≤ (21276202400221/50000000000000 : ℝ)^3183
        have hw : |(1047792789/2000000000 : ℝ)|=(1047792789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8671163/39062500 : ℝ)|^4207 ≤ (13677970437033/100000000000000 : ℝ)^3183
        have hw : |(-8671163/39062500 : ℝ)|=(8671163/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s3_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543982209/1250000000 : ℝ)*x 0 + (4171242723/10000000000 : ℝ)*x 1 + (2270050243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543982209/1250000000 : ℝ)^4207 ≤ (16649571184041/50000000000000 : ℝ)^3183 := by
    have hnat : (543982209 : ℕ)^4207*50000000000000^3183 ≤ 16649571184041^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543982209 1250000000 16649571184041 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171242723/10000000000 : ℝ)^4207 ≤ (15742417198083/50000000000000 : ℝ)^3183 := by
    have hnat : (4171242723 : ℕ)^4207*50000000000000^3183 ≤ 15742417198083^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171242723 10000000000 15742417198083 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270050243/5000000000 : ℝ)^4207 ≤ (35216023229679/100000000000000 : ℝ)^3183 := by
    have hnat : (2270050243 : ℕ)^4207*100000000000000^3183 ≤ 35216023229679^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270050243 5000000000 35216023229679 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543982209/1250000000 : ℝ), (4171242723/10000000000 : ℝ), (2270050243/5000000000 : ℝ)] ![(16649571184041/50000000000000 : ℝ), (15742417198083/50000000000000 : ℝ), (35216023229679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543982209/1250000000 : ℝ)|^4207 ≤ (16649571184041/50000000000000 : ℝ)^3183
        have hw : |(543982209/1250000000 : ℝ)|=(543982209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171242723/10000000000 : ℝ)|^4207 ≤ (15742417198083/50000000000000 : ℝ)^3183
        have hw : |(4171242723/10000000000 : ℝ)|=(4171242723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2270050243/5000000000 : ℝ)|^4207 ≤ (35216023229679/100000000000000 : ℝ)^3183
        have hw : |(2270050243/5000000000 : ℝ)|=(2270050243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s3_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063329689/5000000000 : ℝ)*x 0 + (654954447/1250000000 : ℝ)*x 1 + (5420859341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063329689/5000000000 : ℝ)^4207 ≤ (3231113887603/25000000000000 : ℝ)^3183 := by
    have hnat : (1063329689 : ℕ)^4207*25000000000000^3183 ≤ 3231113887603^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063329689 5000000000 3231113887603 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654954447/1250000000 : ℝ)^4207 ≤ (2659975944739/6250000000000 : ℝ)^3183 := by
    have hnat : (654954447 : ℕ)^4207*6250000000000^3183 ≤ 2659975944739^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654954447 1250000000 2659975944739 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420859341/10000000000 : ℝ)^4207 ≤ (44515929309789/100000000000000 : ℝ)^3183 := by
    have hnat : (5420859341 : ℕ)^4207*100000000000000^3183 ≤ 44515929309789^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420859341 10000000000 44515929309789 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063329689/5000000000 : ℝ), (654954447/1250000000 : ℝ), (5420859341/10000000000 : ℝ)] ![(3231113887603/25000000000000 : ℝ), (2659975944739/6250000000000 : ℝ), (44515929309789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063329689/5000000000 : ℝ)|^4207 ≤ (3231113887603/25000000000000 : ℝ)^3183
        have hw : |(-1063329689/5000000000 : ℝ)|=(1063329689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654954447/1250000000 : ℝ)|^4207 ≤ (2659975944739/6250000000000 : ℝ)^3183
        have hw : |(654954447/1250000000 : ℝ)|=(654954447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420859341/10000000000 : ℝ)|^4207 ≤ (44515929309789/100000000000000 : ℝ)^3183
        have hw : |(5420859341/10000000000 : ℝ)|=(5420859341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s3_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305446561/10000000000 : ℝ)*x 0 + (-2037922247/10000000000 : ℝ)*x 1 + (2710429499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305446561/10000000000 : ℝ)^4207 ≤ (10816892242319/25000000000000 : ℝ)^3183 := by
    have hnat : (5305446561 : ℕ)^4207*25000000000000^3183 ≤ 10816892242319^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305446561 10000000000 10816892242319 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2037922247/10000000000 : ℝ)^4207 ≤ (12216505429239/100000000000000 : ℝ)^3183 := by
    have hnat : (2037922247 : ℕ)^4207*100000000000000^3183 ≤ 12216505429239^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037922247 10000000000 12216505429239 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710429499/5000000000 : ℝ)^4207 ≤ (11128981396731/25000000000000 : ℝ)^3183 := by
    have hnat : (2710429499 : ℕ)^4207*25000000000000^3183 ≤ 11128981396731^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710429499 5000000000 11128981396731 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305446561/10000000000 : ℝ), (-2037922247/10000000000 : ℝ), (2710429499/5000000000 : ℝ)] ![(10816892242319/25000000000000 : ℝ), (12216505429239/100000000000000 : ℝ), (11128981396731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305446561/10000000000 : ℝ)|^4207 ≤ (10816892242319/25000000000000 : ℝ)^3183
        have hw : |(5305446561/10000000000 : ℝ)|=(5305446561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2037922247/10000000000 : ℝ)|^4207 ≤ (12216505429239/100000000000000 : ℝ)^3183
        have hw : |(-2037922247/10000000000 : ℝ)|=(2037922247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710429499/5000000000 : ℝ)|^4207 ≤ (11128981396731/25000000000000 : ℝ)^3183
        have hw : |(2710429499/5000000000 : ℝ)|=(2710429499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s3_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305446327/10000000000 : ℝ)*x 0 + (5420858987/10000000000 : ℝ)*x 1 + (-101896129/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305446327/10000000000 : ℝ)^4207 ≤ (21633783223501/50000000000000 : ℝ)^3183 := by
    have hnat : (5305446327 : ℕ)^4207*50000000000000^3183 ≤ 21633783223501^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305446327 10000000000 21633783223501 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420858987/10000000000 : ℝ)^4207 ≤ (11128981366883/25000000000000 : ℝ)^3183 := by
    have hnat : (5420858987 : ℕ)^4207*25000000000000^3183 ≤ 11128981366883^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420858987 10000000000 11128981366883 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101896129/500000000 : ℝ)^4207 ≤ (763531754227/6250000000000 : ℝ)^3183 := by
    have hnat : (101896129 : ℕ)^4207*6250000000000^3183 ≤ 763531754227^3183*500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101896129 500000000 763531754227 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305446327/10000000000 : ℝ), (5420858987/10000000000 : ℝ), (-101896129/500000000 : ℝ)] ![(21633783223501/50000000000000 : ℝ), (11128981366883/25000000000000 : ℝ), (763531754227/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305446327/10000000000 : ℝ)|^4207 ≤ (21633783223501/50000000000000 : ℝ)^3183
        have hw : |(5305446327/10000000000 : ℝ)|=(5305446327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420858987/10000000000 : ℝ)|^4207 ≤ (11128981366883/25000000000000 : ℝ)^3183
        have hw : |(5420858987/10000000000 : ℝ)|=(5420858987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101896129/500000000 : ℝ)|^4207 ≤ (763531754227/6250000000000 : ℝ)^3183
        have hw : |(-101896129/500000000 : ℝ)|=(101896129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s3_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351887761/10000000000 : ℝ)*x 0 + (1134685489/2500000000 : ℝ)*x 1 + (834521631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351887761/10000000000 : ℝ)^4207 ≤ (1040607708389/3125000000000 : ℝ)^3183 := by
    have hnat : (4351887761 : ℕ)^4207*3125000000000^3183 ≤ 1040607708389^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351887761 10000000000 1040607708389 3125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134685489/2500000000 : ℝ)^4207 ≤ (1408083847299/4000000000000 : ℝ)^3183 := by
    have hnat : (1134685489 : ℕ)^4207*4000000000000^3183 ≤ 1408083847299^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134685489 2500000000 1408083847299 4000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834521631/2000000000 : ℝ)^4207 ≤ (31498457145543/100000000000000 : ℝ)^3183 := by
    have hnat : (834521631 : ℕ)^4207*100000000000000^3183 ≤ 31498457145543^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834521631 2000000000 31498457145543 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351887761/10000000000 : ℝ), (1134685489/2500000000 : ℝ), (834521631/2000000000 : ℝ)] ![(1040607708389/3125000000000 : ℝ), (1408083847299/4000000000000 : ℝ), (31498457145543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351887761/10000000000 : ℝ)|^4207 ≤ (1040607708389/3125000000000 : ℝ)^3183
        have hw : |(4351887761/10000000000 : ℝ)|=(4351887761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134685489/2500000000 : ℝ)|^4207 ≤ (1408083847299/4000000000000 : ℝ)^3183
        have hw : |(1134685489/2500000000 : ℝ)|=(1134685489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834521631/2000000000 : ℝ)|^4207 ≤ (31498457145543/100000000000000 : ℝ)^3183
        have hw : |(834521631/2000000000 : ℝ)|=(834521631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1357/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14721/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9413/100000 : ℝ) ^ (8413/2048 : ℝ) ≤ (243347596155451/4000000000000000000 : ℝ) := by
    have hpowers : (9413/100000 : ℝ)^8413 ≤ (243347596155451/4000000000000000000 : ℝ)^2048 := by
      have hnat : (9413 : ℕ)^8413*4000000000000000000^2048 ≤ 243347596155451^2048*100000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9413 100000 243347596155451 4000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9413/100000 : ℝ)) (X := (243347596155451/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16279/100000 : ℝ) ^ (8413/2048 : ℝ) ≤ (57734780244118153/100000000000000000000 : ℝ) := by
    have hpowers : (16279/100000 : ℝ)^8413 ≤ (57734780244118153/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16279 : ℕ)^8413*100000000000000000000^2048 ≤ 57734780244118153^2048*100000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16279 100000 57734780244118153 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16279/100000 : ℝ)) (X := (57734780244118153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000243347596155451/2000000000000000000 : ℝ) ≤ (2500074045070087/2500000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (2000243347596155451/2000000000000000000 : ℝ)^2048 ≤ (2500074045070087/2500000000000000 : ℝ)^8413 := by
      have hnat : (2000243347596155451 : ℕ)^2048*2500000000000000^8413 ≤ 2500074045070087^8413*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000243347596155451 2000000000000000000 2500074045070087 2500000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074045070087/2500000000000000 : ℝ)) (X := (2000243347596155451/2000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25015954617537001107/25000000000000000000 : ℝ) ≤ (5000776587933423/5000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (25015954617537001107/25000000000000000000 : ℝ)^2048 ≤ (5000776587933423/5000000000000000 : ℝ)^8413 := by
      have hnat : (25015954617537001107 : ℕ)^2048*5000000000000000^8413 ≤ 5000776587933423^8413*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015954617537001107 25000000000000000000 5000776587933423 5000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000776587933423/5000000000000000 : ℝ)) (X := (25015954617537001107/25000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50057734780244118153/50000000000000000000 : ℝ) ≤ (312587817857917/312500000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50057734780244118153/50000000000000000000 : ℝ)^2048 ≤ (312587817857917/312500000000000 : ℝ)^8413 := by
      have hnat : (50057734780244118153 : ℕ)^2048*312500000000000^8413 ≤ 312587817857917^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057734780244118153 50000000000000000000 312587817857917 312500000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312587817857917/312500000000000 : ℝ)) (X := (50057734780244118153/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(243347596155451/4000000000000000000 : ℝ) ≤ ((3431918468744672901/3433000000000000000 : ℝ)+2*(628497793249/343300000000000 : ℝ)*(9413/100000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (3431918468744672901/3433000000000000000 : ℝ)+2*(628497793249/343300000000000 : ℝ)*(9413/100000 : ℝ)=(2500074045070087/2500000000000000 : ℝ) by norm_num, show 1+2*(243347596155451/4000000000000000000 : ℝ)=(2000243347596155451/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57734780244118153/100000000000000000000 : ℝ)+(243347596155451/4000000000000000000 : ℝ) ≤ ((3431918468744672901/3433000000000000000 : ℝ)+(628497793249/343300000000000 : ℝ)*((16279/100000 : ℝ)+(9413/100000 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (3431918468744672901/3433000000000000000 : ℝ)+(628497793249/343300000000000 : ℝ)*((16279/100000 : ℝ)+(9413/100000 : ℝ))=(5000776587933423/5000000000000000 : ℝ) by norm_num, show 1+(57734780244118153/100000000000000000000 : ℝ)+(243347596155451/4000000000000000000 : ℝ)=(25015954617537001107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57734780244118153/100000000000000000000 : ℝ) ≤ ((3431918468744672901/3433000000000000000 : ℝ)+2*(628497793249/343300000000000 : ℝ)*(16279/100000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (3431918468744672901/3433000000000000000 : ℝ)+2*(628497793249/343300000000000 : ℝ)*(16279/100000 : ℝ)=(312587817857917/312500000000000 : ℝ) by norm_num, show 1+2*(57734780244118153/100000000000000000000 : ℝ)=(50057734780244118153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3431918468744672901/3433000000000000000 : ℝ)*(X 1 0+X 2 0)+(628497793249/343300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (9413/100000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (3431918468744672901/3433000000000000000 : ℝ)) (alpha := (628497793249/343300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3431918468744672901/3433000000000000000 : ℝ)*(X 0 1+X 2 1)+(628497793249/343300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (9413/100000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (3431918468744672901/3433000000000000000 : ℝ)) (alpha := (628497793249/343300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3431918468744672901/3433000000000000000 : ℝ)*(X 0 2+X 1 2)+(628497793249/343300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (9413/100000 : ℝ)) (hi := (16279/100000 : ℝ)) (c := (3431918468744672901/3433000000000000000 : ℝ)) (alpha := (628497793249/343300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531661117/2500000000 : ℝ)*X 0 0+(542153527/1000000000 : ℝ)*X 0 1+(2619481671/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351958671/10000000000 : ℝ)*X 1 0+(-110990903/500000000 : ℝ)*X 1 1+(2619481777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351958533/10000000000 : ℝ)*X 2 0+(1047792789/2000000000 : ℝ)*X 2 1+(-8671163/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543982209/1250000000 : ℝ)*X 0 0+(4171242723/10000000000 : ℝ)*X 0 1+(2270050243/5000000000 : ℝ)*X 0 2+(543982209/1250000000 : ℝ)*X 1 0+(4171242723/10000000000 : ℝ)*X 1 1+(2270050243/5000000000 : ℝ)*X 1 2+(543982209/1250000000 : ℝ)*X 2 0+(4171242723/10000000000 : ℝ)*X 2 1+(2270050243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063329689/5000000000 : ℝ)*X 0 0+(654954447/1250000000 : ℝ)*X 0 1+(5420859341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305446561/10000000000 : ℝ)*X 1 0+(-2037922247/10000000000 : ℝ)*X 1 1+(2710429499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305446327/10000000000 : ℝ)*X 2 0+(5420858987/10000000000 : ℝ)*X 2 1+(-101896129/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351887761/10000000000 : ℝ)*X 0 0+(1134685489/2500000000 : ℝ)*X 0 1+(834521631/2000000000 : ℝ)*X 0 2+(4351887761/10000000000 : ℝ)*X 1 0+(1134685489/2500000000 : ℝ)*X 1 1+(834521631/2000000000 : ℝ)*X 1 2+(4351887761/10000000000 : ℝ)*X 2 0+(1134685489/2500000000 : ℝ)*X 2 1+(834521631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (949946257542945354524513193/85825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215178409/12500000000000 : ℝ)*(base19) + (32115033/2500000000000 : ℝ)*(base23) + (15819961/10000000000000 : ℝ)*(lower2) + (39264347/50000000000000 : ℝ)*(upper3) + (51274179/25000000000000 : ℝ)*(upper5) + (2047122113990723/50000000000000 : ℝ)*(major0) + (2047122113990723/50000000000000 : ℝ)*(major1) + (2047122113990723/50000000000000 : ℝ)*(major2) + (2738666746861819/50000000000000 : ℝ)*(sp0) + (2738689448227021/50000000000000 : ℝ)*(sp1) + (5477379333279993/100000000000000 : ℝ)*(sp2) + (1355545149806747/50000000000000 : ℝ)*(sp3) + (11781039419/25000000000000 : ℝ)*(sp4) + (268273767/1562500000000 : ℝ)*(sp7) + (1355553734567291/50000000000000 : ℝ)*(f.failure) + (5477380617881313/100000000000000 : ℝ)*(f.sum) + (27650796714547/8582500000000000000000000000 : ℝ)*base65 + (317224612475867423/171650000000000000000000000000000 : ℝ)*base67 + (1009816139834367423/171650000000000000000000000000000 : ℝ)*base69 + (565007877219067423/171650000000000000000000000000000 : ℝ)*base71 + (2697054449001/4291250000000000000000000000 : ℝ)*base73 + (1934725463646967423/171650000000000000000000000000000 : ℝ)*base75 + (2593974029485517423/171650000000000000000000000000000 : ℝ)*base77 + (2606338928210017423/171650000000000000000000000000000 : ℝ)*base79 + (10502060586377/8582500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (181223/78125000000000000000 : ℝ)*base90 + (181223/78125000000000000000 : ℝ)*base92 + (181223/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174810194562355026241777833/17165000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2319773521/100000000000000 : ℝ)*(base19) + (2218185173/100000000000000 : ℝ)*(base23) + (59400813/100000000000000 : ℝ)*(upper3) + (143149171/100000000000000 : ℝ)*(lower4) + (370854653/100000000000000 : ℝ)*(upper5) + (824928098049289/20000000000000 : ℝ)*(major0) + (824928098049289/20000000000000 : ℝ)*(major1) + (824928098049289/20000000000000 : ℝ)*(major2) + (44728290781/100000000000000 : ℝ)*(sp1) + (30124695487/100000000000000 : ℝ)*(sp2) + (2759022758645067/50000000000000 : ℝ)*(sp4) + (689749808653229/12500000000000 : ℝ)*(sp5) + (2759006587204737/50000000000000 : ℝ)*(sp6) + (68280878093313/2500000000000 : ℝ)*(sp7) + (68280878093313/2500000000000 : ℝ)*(f.failure) + (2759022758645067/50000000000000 : ℝ)*(f.sum) + (11421738646483/3433000000000000000000000000 : ℝ)*base66 + (486904597547587389/68660000000000000000000000000000 : ℝ)*base67 + (50760761074187389/68660000000000000000000000000000 : ℝ)*base69 + (58368900508952611/68660000000000000000000000000000 : ℝ)*base72 + (10746142427613/3433000000000000000000000000 : ℝ)*base73 + (602554381977627389/68660000000000000000000000000000 : ℝ)*base75 + (572996411337487389/68660000000000000000000000000000 : ℝ)*base77 + (704704288222047389/68660000000000000000000000000000 : ℝ)*base79 + (9047040116391/3433000000000000000000000000 : ℝ)*base82 + (34603/7812500000000000000 : ℝ)*base90 + (34603/7812500000000000000 : ℝ)*base92 + (34603/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1221_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1357/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1221_s4_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129071303/10000000000 : ℝ)*x 0 + (1349590901/2500000000 : ℝ)*x 1 + (2630272603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129071303/10000000000 : ℝ)^4207 ≤ (12943832847399/100000000000000 : ℝ)^3183 := by
    have hnat : (2129071303 : ℕ)^4207*100000000000000^3183 ≤ 12943832847399^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129071303 10000000000 12943832847399 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349590901/2500000000 : ℝ)^4207 ≤ (22135963725567/50000000000000 : ℝ)^3183 := by
    have hnat : (1349590901 : ℕ)^4207*50000000000000^3183 ≤ 22135963725567^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349590901 2500000000 22135963725567 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630272603/5000000000 : ℝ)^4207 ≤ (42784239692339/100000000000000 : ℝ)^3183 := by
    have hnat : (2630272603 : ℕ)^4207*100000000000000^3183 ≤ 42784239692339^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630272603 5000000000 42784239692339 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129071303/10000000000 : ℝ), (1349590901/2500000000 : ℝ), (2630272603/5000000000 : ℝ)] ![(12943832847399/100000000000000 : ℝ), (22135963725567/50000000000000 : ℝ), (42784239692339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129071303/10000000000 : ℝ)|^4207 ≤ (12943832847399/100000000000000 : ℝ)^3183
        have hw : |(-2129071303/10000000000 : ℝ)|=(2129071303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349590901/2500000000 : ℝ)|^4207 ≤ (22135963725567/50000000000000 : ℝ)^3183
        have hw : |(1349590901/2500000000 : ℝ)|=(1349590901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630272603/5000000000 : ℝ)|^4207 ≤ (42784239692339/100000000000000 : ℝ)^3183
        have hw : |(2630272603/5000000000 : ℝ)|=(2630272603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s4_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673064041/5000000000 : ℝ)*x 0 + (-1099528383/5000000000 : ℝ)*x 1 + (5260545229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673064041/5000000000 : ℝ)^4207 ≤ (4370661293787/10000000000000 : ℝ)^3183 := by
    have hnat : (2673064041 : ℕ)^4207*10000000000000^3183 ≤ 4370661293787^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673064041 5000000000 4370661293787 10000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099528383/5000000000 : ℝ)^4207 ≤ (13509147108617/100000000000000 : ℝ)^3183 := by
    have hnat : (1099528383 : ℕ)^4207*100000000000000^3183 ≤ 13509147108617^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099528383 5000000000 13509147108617 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260545229/10000000000 : ℝ)^4207 ≤ (21392119969789/50000000000000 : ℝ)^3183 := by
    have hnat : (5260545229 : ℕ)^4207*50000000000000^3183 ≤ 21392119969789^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260545229 10000000000 21392119969789 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673064041/5000000000 : ℝ), (-1099528383/5000000000 : ℝ), (5260545229/10000000000 : ℝ)] ![(4370661293787/10000000000000 : ℝ), (13509147108617/100000000000000 : ℝ), (21392119969789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673064041/5000000000 : ℝ)|^4207 ≤ (4370661293787/10000000000000 : ℝ)^3183
        have hw : |(2673064041/5000000000 : ℝ)|=(2673064041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1099528383/5000000000 : ℝ)|^4207 ≤ (13509147108617/100000000000000 : ℝ)^3183
        have hw : |(-1099528383/5000000000 : ℝ)|=(1099528383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260545229/10000000000 : ℝ)|^4207 ≤ (21392119969789/50000000000000 : ℝ)^3183
        have hw : |(5260545229/10000000000 : ℝ)|=(5260545229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s4_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673064041/5000000000 : ℝ)*x 0 + (5260545241/10000000000 : ℝ)*x 1 + (-8796227/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673064041/5000000000 : ℝ)^4207 ≤ (4370661293787/10000000000000 : ℝ)^3183 := by
    have hnat : (2673064041 : ℕ)^4207*10000000000000^3183 ≤ 4370661293787^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673064041 5000000000 4370661293787 10000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260545241/10000000000 : ℝ)^4207 ≤ (10696060017143/25000000000000 : ℝ)^3183 := by
    have hnat : (5260545241 : ℕ)^4207*25000000000000^3183 ≤ 10696060017143^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260545241 10000000000 10696060017143 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8796227/40000000 : ℝ)^4207 ≤ (2701829395741/20000000000000 : ℝ)^3183 := by
    have hnat : (8796227 : ℕ)^4207*20000000000000^3183 ≤ 2701829395741^3183*40000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8796227 40000000 2701829395741 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673064041/5000000000 : ℝ), (5260545241/10000000000 : ℝ), (-8796227/40000000 : ℝ)] ![(4370661293787/10000000000000 : ℝ), (10696060017143/25000000000000 : ℝ), (2701829395741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673064041/5000000000 : ℝ)|^4207 ≤ (4370661293787/10000000000000 : ℝ)^3183
        have hw : |(2673064041/5000000000 : ℝ)|=(2673064041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260545241/10000000000 : ℝ)|^4207 ≤ (10696060017143/25000000000000 : ℝ)^3183
        have hw : |(5260545241/10000000000 : ℝ)|=(5260545241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8796227/40000000 : ℝ)|^4207 ≤ (2701829395741/20000000000000 : ℝ)^3183
        have hw : |(-8796227/40000000 : ℝ)|=(8796227/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s4_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353311173/10000000000 : ℝ)*x 0 + (1054066223/2500000000 : ℝ)*x 1 + (2247353041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353311173/10000000000 : ℝ)^4207 ≤ (8328460723763/25000000000000 : ℝ)^3183 := by
    have hnat : (4353311173 : ℕ)^4207*25000000000000^3183 ≤ 8328460723763^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353311173 10000000000 8328460723763 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054066223/2500000000 : ℝ)^4207 ≤ (1995923086673/6250000000000 : ℝ)^3183 := by
    have hnat : (1054066223 : ℕ)^4207*6250000000000^3183 ≤ 1995923086673^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054066223 2500000000 1995923086673 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247353041/5000000000 : ℝ)^4207 ≤ (34751387709953/100000000000000 : ℝ)^3183 := by
    have hnat : (2247353041 : ℕ)^4207*100000000000000^3183 ≤ 34751387709953^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247353041 5000000000 34751387709953 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353311173/10000000000 : ℝ), (1054066223/2500000000 : ℝ), (2247353041/5000000000 : ℝ)] ![(8328460723763/25000000000000 : ℝ), (1995923086673/6250000000000 : ℝ), (34751387709953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353311173/10000000000 : ℝ)|^4207 ≤ (8328460723763/25000000000000 : ℝ)^3183
        have hw : |(4353311173/10000000000 : ℝ)|=(4353311173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054066223/2500000000 : ℝ)|^4207 ≤ (1995923086673/6250000000000 : ℝ)^3183
        have hw : |(1054066223/2500000000 : ℝ)|=(1054066223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247353041/5000000000 : ℝ)|^4207 ≤ (34751387709953/100000000000000 : ℝ)^3183
        have hw : |(2247353041/5000000000 : ℝ)|=(2247353041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s4_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129076867/10000000000 : ℝ)*x 0 + (2630464527/5000000000 : ℝ)*x 1 + (2698989401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129076867/10000000000 : ℝ)^4207 ≤ (3235969389123/25000000000000 : ℝ)^3183 := by
    have hnat : (2129076867 : ℕ)^4207*25000000000000^3183 ≤ 3235969389123^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129076867 10000000000 3235969389123 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630464527/5000000000 : ℝ)^4207 ≤ (42788365921219/100000000000000 : ℝ)^3183 := by
    have hnat : (2630464527 : ℕ)^4207*100000000000000^3183 ≤ 42788365921219^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630464527 5000000000 42788365921219 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698989401/5000000000 : ℝ)^4207 ≤ (44267756505669/100000000000000 : ℝ)^3183 := by
    have hnat : (2698989401 : ℕ)^4207*100000000000000^3183 ≤ 44267756505669^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698989401 5000000000 44267756505669 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129076867/10000000000 : ℝ), (2630464527/5000000000 : ℝ), (2698989401/5000000000 : ℝ)] ![(3235969389123/25000000000000 : ℝ), (42788365921219/100000000000000 : ℝ), (44267756505669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129076867/10000000000 : ℝ)|^4207 ≤ (3235969389123/25000000000000 : ℝ)^3183
        have hw : |(-2129076867/10000000000 : ℝ)|=(2129076867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630464527/5000000000 : ℝ)|^4207 ≤ (42788365921219/100000000000000 : ℝ)^3183
        have hw : |(2630464527/5000000000 : ℝ)|=(2630464527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698989401/5000000000 : ℝ)|^4207 ≤ (44267756505669/100000000000000 : ℝ)^3183
        have hw : |(2698989401/5000000000 : ℝ)|=(2698989401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s4_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13277539/25000000 : ℝ)*x 0 + (-515405889/2500000000 : ℝ)*x 1 + (539797809/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13277539/25000000 : ℝ)^4207 ≤ (21663803745349/50000000000000 : ℝ)^3183 := by
    have hnat : (13277539 : ℕ)^4207*50000000000000^3183 ≤ 21663803745349^3183*25000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13277539 25000000 21663803745349 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515405889/2500000000 : ℝ)^4207 ≤ (2480928741679/20000000000000 : ℝ)^3183 := by
    have hnat : (515405889 : ℕ)^4207*20000000000000^3183 ≤ 2480928741679^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515405889 2500000000 2480928741679 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539797809/1000000000 : ℝ)^4207 ≤ (5533468598531/12500000000000 : ℝ)^3183 := by
    have hnat : (539797809 : ℕ)^4207*12500000000000^3183 ≤ 5533468598531^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539797809 1000000000 5533468598531 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13277539/25000000 : ℝ), (-515405889/2500000000 : ℝ), (539797809/1000000000 : ℝ)] ![(21663803745349/50000000000000 : ℝ), (2480928741679/20000000000000 : ℝ), (5533468598531/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13277539/25000000 : ℝ)|^4207 ≤ (21663803745349/50000000000000 : ℝ)^3183
        have hw : |(13277539/25000000 : ℝ)|=(13277539/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515405889/2500000000 : ℝ)|^4207 ≤ (2480928741679/20000000000000 : ℝ)^3183
        have hw : |(-515405889/2500000000 : ℝ)|=(515405889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539797809/1000000000 : ℝ)|^4207 ≤ (5533468598531/12500000000000 : ℝ)^3183
        have hw : |(539797809/1000000000 : ℝ)|=(539797809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s4_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82984621/156250000 : ℝ)*x 0 + (107959561/200000000 : ℝ)*x 1 + (-257702927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82984621/156250000 : ℝ)^4207 ≤ (43327609043391/100000000000000 : ℝ)^3183 := by
    have hnat : (82984621 : ℕ)^4207*100000000000000^3183 ≤ 43327609043391^3183*156250000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82984621 156250000 43327609043391 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107959561/200000000 : ℝ)^4207 ≤ (8853549670937/20000000000000 : ℝ)^3183 := by
    have hnat : (107959561 : ℕ)^4207*20000000000000^3183 ≤ 8853549670937^3183*200000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107959561 200000000 8853549670937 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257702927/1250000000 : ℝ)^4207 ≤ (12404642595027/100000000000000 : ℝ)^3183 := by
    have hnat : (257702927 : ℕ)^4207*100000000000000^3183 ≤ 12404642595027^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257702927 1250000000 12404642595027 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82984621/156250000 : ℝ), (107959561/200000000 : ℝ), (-257702927/1250000000 : ℝ)] ![(43327609043391/100000000000000 : ℝ), (8853549670937/20000000000000 : ℝ), (12404642595027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82984621/156250000 : ℝ)|^4207 ≤ (43327609043391/100000000000000 : ℝ)^3183
        have hw : |(82984621/156250000 : ℝ)|=(82984621/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107959561/200000000 : ℝ)|^4207 ≤ (8853549670937/20000000000000 : ℝ)^3183
        have hw : |(107959561/200000000 : ℝ)|=(107959561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257702927/1250000000 : ℝ)|^4207 ≤ (12404642595027/100000000000000 : ℝ)^3183
        have hw : |(-257702927/1250000000 : ℝ)|=(257702927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s4_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2176662129/5000000000 : ℝ)*x 0 + (2246965261/5000000000 : ℝ)*x 1 + (1054260827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176662129/5000000000 : ℝ)^4207 ≤ (1332559009691/4000000000000 : ℝ)^3183 := by
    have hnat : (2176662129 : ℕ)^4207*4000000000000^3183 ≤ 1332559009691^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176662129 5000000000 1332559009691 4000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246965261/5000000000 : ℝ)^4207 ≤ (43429328141/125000000000 : ℝ)^3183 := by
    have hnat : (2246965261 : ℕ)^4207*125000000000^3183 ≤ 43429328141^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246965261 5000000000 43429328141 125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054260827/2500000000 : ℝ)^4207 ≤ (998205069957/3125000000000 : ℝ)^3183 := by
    have hnat : (1054260827 : ℕ)^4207*3125000000000^3183 ≤ 998205069957^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054260827 2500000000 998205069957 3125000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176662129/5000000000 : ℝ), (2246965261/5000000000 : ℝ), (1054260827/2500000000 : ℝ)] ![(1332559009691/4000000000000 : ℝ), (43429328141/125000000000 : ℝ), (998205069957/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176662129/5000000000 : ℝ)|^4207 ≤ (1332559009691/4000000000000 : ℝ)^3183
        have hw : |(2176662129/5000000000 : ℝ)|=(2176662129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246965261/5000000000 : ℝ)|^4207 ≤ (43429328141/125000000000 : ℝ)^3183
        have hw : |(2246965261/5000000000 : ℝ)|=(2246965261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054260827/2500000000 : ℝ)|^4207 ≤ (998205069957/3125000000000 : ℝ)^3183
        have hw : |(1054260827/2500000000 : ℝ)|=(1054260827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1357/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11317/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1357/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1357/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1357/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1357/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1357/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1357/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1357/12500 : ℝ) ^ (8413/2048 : ℝ) ≤ (2732488409482427/25000000000000000000 : ℝ) := by
    have hpowers : (1357/12500 : ℝ)^8413 ≤ (2732488409482427/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1357 : ℕ)^8413*25000000000000000000^2048 ≤ 2732488409482427^2048*12500^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1357 12500 2732488409482427 25000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1357/12500 : ℝ)) (X := (2732488409482427/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14721/100000 : ℝ) ^ (8413/2048 : ℝ) ≤ (7638203623736297/20000000000000000000 : ℝ) := by
    have hpowers : (14721/100000 : ℝ)^8413 ≤ (7638203623736297/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14721 : ℕ)^8413*20000000000000000000^2048 ≤ 7638203623736297^2048*100000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14721 100000 7638203623736297 20000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14721/100000 : ℝ)) (X := (7638203623736297/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502732488409482427/12500000000000000000 : ℝ) ≤ (400021283912283/400000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (12502732488409482427/12500000000000000000 : ℝ)^2048 ≤ (400021283912283/400000000000000 : ℝ)^8413 := by
      have hnat : (12502732488409482427 : ℕ)^2048*400000000000000^8413 ≤ 400021283912283^8413*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502732488409482427 12500000000000000000 400021283912283 400000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400021283912283/400000000000000 : ℝ)) (X := (12502732488409482427/12500000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049120971756611193/100000000000000000000 : ℝ) ≤ (10001195543354691/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (100049120971756611193/100000000000000000000 : ℝ)^2048 ≤ (10001195543354691/10000000000000000 : ℝ)^8413 := by
      have hnat : (100049120971756611193 : ℕ)^2048*10000000000000000^8413 ≤ 10001195543354691^8413*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049120971756611193 100000000000000000000 10001195543354691 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001195543354691/10000000000000000 : ℝ)) (X := (100049120971756611193/100000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007638203623736297/10000000000000000000 : ℝ) ≤ (10001858988902307/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (10007638203623736297/10000000000000000000 : ℝ)^2048 ≤ (10001858988902307/10000000000000000 : ℝ)^8413 := by
      have hnat : (10007638203623736297 : ℕ)^2048*10000000000000000^8413 ≤ 10001858988902307^8413*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007638203623736297 10000000000000000000 10001858988902307 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001858988902307/10000000000000000 : ℝ)) (X := (10007638203623736297/10000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2732488409482427/25000000000000000000 : ℝ) ≤ ((38637651828294506283/38650000000000000000 : ℝ)+2*(20732673363/12078125000000 : ℝ)*(1357/12500 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (38637651828294506283/38650000000000000000 : ℝ)+2*(20732673363/12078125000000 : ℝ)*(1357/12500 : ℝ)=(400021283912283/400000000000000 : ℝ) by norm_num, show 1+2*(2732488409482427/25000000000000000000 : ℝ)=(12502732488409482427/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7638203623736297/20000000000000000000 : ℝ)+(2732488409482427/25000000000000000000 : ℝ) ≤ ((38637651828294506283/38650000000000000000 : ℝ)+(20732673363/12078125000000 : ℝ)*((14721/100000 : ℝ)+(1357/12500 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (38637651828294506283/38650000000000000000 : ℝ)+(20732673363/12078125000000 : ℝ)*((14721/100000 : ℝ)+(1357/12500 : ℝ))=(10001195543354691/10000000000000000 : ℝ) by norm_num, show 1+(7638203623736297/20000000000000000000 : ℝ)+(2732488409482427/25000000000000000000 : ℝ)=(100049120971756611193/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7638203623736297/20000000000000000000 : ℝ) ≤ ((38637651828294506283/38650000000000000000 : ℝ)+2*(20732673363/12078125000000 : ℝ)*(14721/100000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (38637651828294506283/38650000000000000000 : ℝ)+2*(20732673363/12078125000000 : ℝ)*(14721/100000 : ℝ)=(10001858988902307/10000000000000000 : ℝ) by norm_num, show 1+2*(7638203623736297/20000000000000000000 : ℝ)=(10007638203623736297/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38637651828294506283/38650000000000000000 : ℝ)*(X 1 0+X 2 0)+(20732673363/12078125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (1357/12500 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (38637651828294506283/38650000000000000000 : ℝ)) (alpha := (20732673363/12078125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38637651828294506283/38650000000000000000 : ℝ)*(X 0 1+X 2 1)+(20732673363/12078125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (1357/12500 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (38637651828294506283/38650000000000000000 : ℝ)) (alpha := (20732673363/12078125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38637651828294506283/38650000000000000000 : ℝ)*(X 0 2+X 1 2)+(20732673363/12078125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (1357/12500 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (38637651828294506283/38650000000000000000 : ℝ)) (alpha := (20732673363/12078125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2129071303/10000000000 : ℝ)*X 0 0+(1349590901/2500000000 : ℝ)*X 0 1+(2630272603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673064041/5000000000 : ℝ)*X 1 0+(-1099528383/5000000000 : ℝ)*X 1 1+(5260545229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673064041/5000000000 : ℝ)*X 2 0+(5260545241/10000000000 : ℝ)*X 2 1+(-8796227/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353311173/10000000000 : ℝ)*X 0 0+(1054066223/2500000000 : ℝ)*X 0 1+(2247353041/5000000000 : ℝ)*X 0 2+(4353311173/10000000000 : ℝ)*X 1 0+(1054066223/2500000000 : ℝ)*X 1 1+(2247353041/5000000000 : ℝ)*X 1 2+(4353311173/10000000000 : ℝ)*X 2 0+(1054066223/2500000000 : ℝ)*X 2 1+(2247353041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2129076867/10000000000 : ℝ)*X 0 0+(2630464527/5000000000 : ℝ)*X 0 1+(2698989401/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((13277539/25000000 : ℝ)*X 1 0+(-515405889/2500000000 : ℝ)*X 1 1+(539797809/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82984621/156250000 : ℝ)*X 2 0+(107959561/200000000 : ℝ)*X 2 1+(-257702927/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176662129/5000000000 : ℝ)*X 0 0+(2246965261/5000000000 : ℝ)*X 0 1+(1054260827/2500000000 : ℝ)*X 0 2+(2176662129/5000000000 : ℝ)*X 1 0+(2246965261/5000000000 : ℝ)*X 1 1+(1054260827/2500000000 : ℝ)*X 1 2+(2176662129/5000000000 : ℝ)*X 2 0+(2246965261/5000000000 : ℝ)*X 2 1+(1054260827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2185624669343023179/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (152501833/20000000000000 : ℝ)*(base19) + (585284077/100000000000000 : ℝ)*(base23) + (94746803/100000000000000 : ℝ)*(lower2) + (120462467/100000000000000 : ℝ)*(upper3) + (12152779/100000000000000 : ℝ)*(upper5) + (43389632808611/800000000000 : ℝ)*(major0) + (43389632808611/800000000000 : ℝ)*(major1) + (43389632808611/800000000000 : ℝ)*(major2) + (3627973164959041/50000000000000 : ℝ)*(sp0) + (1813991078006649/25000000000000 : ℝ)*(sp1) + (1813991122312921/25000000000000 : ℝ)*(sp2) + (3591431336251739/100000000000000 : ℝ)*(sp3) + (18744617679/100000000000000 : ℝ)*(sp4) + (5822828463/50000000000000 : ℝ)*(sp7) + (1795721490954333/50000000000000 : ℝ)*(f.failure) + (3627982537267881/50000000000000 : ℝ)*(f.sum) + (351764957/125000000000000000000000 : ℝ)*base66 + (413642681371181/40000000000000000000000000000 : ℝ)*base67 + (213418381291181/40000000000000000000000000000 : ℝ)*base69 + (343000673548819/40000000000000000000000000000 : ℝ)*base72 + (945705567/125000000000000000000000 : ℝ)*base73 + (323967820068819/40000000000000000000000000000 : ℝ)*base76 + (65330477811181/40000000000000000000000000000 : ℝ)*base77 + (313317424628819/40000000000000000000000000000 : ℝ)*base80 + (851088877/500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1031701/78125000000000000000 : ℝ)*base89 + (1031701/78125000000000000000 : ℝ)*base91 + (1031701/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19111482539924431537293243051/1932500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76866297/10000000000000 : ℝ)*(base19) + (172810181/6250000000000 : ℝ)*(base23) + (115509211/100000000000000 : ℝ)*(lower3) + (400081763/50000000000000 : ℝ)*(lower4) + (5454101363426901/100000000000000 : ℝ)*(major0) + (5454101363426901/100000000000000 : ℝ)*(major1) + (5454101363426901/100000000000000 : ℝ)*(major2) + (11374152123/100000000000000 : ℝ)*(sp0) + (7716387717/100000000000000 : ℝ)*(sp1) + (10372261901/20000000000000 : ℝ)*(sp2) + (7296619724312707/100000000000000 : ℝ)*(sp4) + (3648311306707071/50000000000000 : ℝ)*(sp5) + (7296576472192427/100000000000000 : ℝ)*(sp6) + (1805785649369277/50000000000000 : ℝ)*(sp7) + (1805785649369277/50000000000000 : ℝ)*(f.failure) + (7296631098464829/100000000000000 : ℝ)*(f.sum) + (20109212565733/9662500000000000000000000000 : ℝ)*base65 + (18106380069612681017/3865000000000000000000000000000000 : ℝ)*base68 + (3419149429602681017/3865000000000000000000000000000000 : ℝ)*base70 + (21225169129567318983/3865000000000000000000000000000000 : ℝ)*base71 + (19463607588767/9662500000000000000000000000 : ℝ)*base74 + (77656601455232318983/3865000000000000000000000000000000 : ℝ)*base75 + (63383019537607318983/3865000000000000000000000000000000 : ℝ)*base77 + (31064835639362318983/3865000000000000000000000000000000 : ℝ)*base79 + (40666668730883/9662500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (41031/78125000000000000000 : ℝ)*base90 + (41031/78125000000000000000 : ℝ)*base92 + (41031/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1221_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1357/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1221_s5_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-133097103/625000000 : ℝ)*x 0 + (5392921117/10000000000 : ℝ)*x 1 + (1053134179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133097103/625000000 : ℝ)^4207 ≤ (12947708833129/100000000000000 : ℝ)^3183 := by
    have hnat : (133097103 : ℕ)^4207*100000000000000^3183 ≤ 12947708833129^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133097103 625000000 12947708833129 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392921117/10000000000 : ℝ)^4207 ≤ (22106472071957/50000000000000 : ℝ)^3183 := by
    have hnat : (5392921117 : ℕ)^4207*50000000000000^3183 ≤ 22106472071957^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392921117 10000000000 22106472071957 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053134179/2000000000 : ℝ)^4207 ≤ (42839347005141/100000000000000 : ℝ)^3183 := by
    have hnat : (1053134179 : ℕ)^4207*100000000000000^3183 ≤ 42839347005141^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053134179 2000000000 42839347005141 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133097103/625000000 : ℝ), (5392921117/10000000000 : ℝ), (1053134179/2000000000 : ℝ)] ![(12947708833129/100000000000000 : ℝ), (22106472071957/50000000000000 : ℝ), (42839347005141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133097103/625000000 : ℝ)|^4207 ≤ (12947708833129/100000000000000 : ℝ)^3183
        have hw : |(-133097103/625000000 : ℝ)|=(133097103/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392921117/10000000000 : ℝ)|^4207 ≤ (22106472071957/50000000000000 : ℝ)^3183
        have hw : |(5392921117/10000000000 : ℝ)|=(5392921117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053134179/2000000000 : ℝ)|^4207 ≤ (42839347005141/100000000000000 : ℝ)^3183
        have hw : |(1053134179/2000000000 : ℝ)|=(1053134179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s5_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344754103/10000000000 : ℝ)*x 0 + (-2194096353/10000000000 : ℝ)*x 1 + (5265670903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344754103/10000000000 : ℝ)^4207 ≤ (43691767062659/100000000000000 : ℝ)^3183 := by
    have hnat : (5344754103 : ℕ)^4207*100000000000000^3183 ≤ 43691767062659^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344754103 10000000000 43691767062659 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194096353/10000000000 : ℝ)^4207 ≤ (1683610729333/12500000000000 : ℝ)^3183 := by
    have hnat : (2194096353 : ℕ)^4207*12500000000000^3183 ≤ 1683610729333^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194096353 10000000000 1683610729333 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265670903/10000000000 : ℝ)^4207 ≤ (10709836772791/25000000000000 : ℝ)^3183 := by
    have hnat : (5265670903 : ℕ)^4207*25000000000000^3183 ≤ 10709836772791^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265670903 10000000000 10709836772791 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344754103/10000000000 : ℝ), (-2194096353/10000000000 : ℝ), (5265670903/10000000000 : ℝ)] ![(43691767062659/100000000000000 : ℝ), (1683610729333/12500000000000 : ℝ), (10709836772791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344754103/10000000000 : ℝ)|^4207 ≤ (43691767062659/100000000000000 : ℝ)^3183
        have hw : |(5344754103/10000000000 : ℝ)|=(5344754103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194096353/10000000000 : ℝ)|^4207 ≤ (1683610729333/12500000000000 : ℝ)^3183
        have hw : |(-2194096353/10000000000 : ℝ)|=(2194096353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265670903/10000000000 : ℝ)|^4207 ≤ (10709836772791/25000000000000 : ℝ)^3183
        have hw : |(5265670903/10000000000 : ℝ)|=(5265670903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s5_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83511783/156250000 : ℝ)*x 0 + (5265670943/10000000000 : ℝ)*x 1 + (-2194096287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83511783/156250000 : ℝ)^4207 ≤ (436917671599/1000000000000 : ℝ)^3183 := by
    have hnat : (83511783 : ℕ)^4207*1000000000000^3183 ≤ 436917671599^3183*156250000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83511783 156250000 436917671599 1000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265670943/10000000000 : ℝ)^4207 ≤ (33468240251/78125000000 : ℝ)^3183 := by
    have hnat : (5265670943 : ℕ)^4207*78125000000^3183 ≤ 33468240251^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265670943 10000000000 33468240251 78125000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194096287/10000000000 : ℝ)^4207 ≤ (13468885299169/100000000000000 : ℝ)^3183 := by
    have hnat : (2194096287 : ℕ)^4207*100000000000000^3183 ≤ 13468885299169^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194096287 10000000000 13468885299169 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83511783/156250000 : ℝ), (5265670943/10000000000 : ℝ), (-2194096287/10000000000 : ℝ)] ![(436917671599/1000000000000 : ℝ), (33468240251/78125000000 : ℝ), (13468885299169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83511783/156250000 : ℝ)|^4207 ≤ (436917671599/1000000000000 : ℝ)^3183
        have hw : |(83511783/156250000 : ℝ)|=(83511783/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265670943/10000000000 : ℝ)|^4207 ≤ (33468240251/78125000000 : ℝ)^3183
        have hw : |(5265670943/10000000000 : ℝ)|=(5265670943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194096287/10000000000 : ℝ)|^4207 ≤ (13468885299169/100000000000000 : ℝ)^3183
        have hw : |(-2194096287/10000000000 : ℝ)|=(2194096287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s5_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870719023/2000000000 : ℝ)*x 0 + (2113452197/5000000000 : ℝ)*x 1 + (4483993857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870719023/2000000000 : ℝ)^4207 ≤ (16658357416621/50000000000000 : ℝ)^3183 := by
    have hnat : (870719023 : ℕ)^4207*50000000000000^3183 ≤ 16658357416621^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870719023 2000000000 16658357416621 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113452197/5000000000 : ℝ)^4207 ≤ (16020661627081/50000000000000 : ℝ)^3183 := by
    have hnat : (2113452197 : ℕ)^4207*50000000000000^3183 ≤ 16020661627081^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113452197 5000000000 16020661627081 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483993857/10000000000 : ℝ)^4207 ≤ (34641961892713/100000000000000 : ℝ)^3183 := by
    have hnat : (4483993857 : ℕ)^4207*100000000000000^3183 ≤ 34641961892713^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483993857 10000000000 34641961892713 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870719023/2000000000 : ℝ), (2113452197/5000000000 : ℝ), (4483993857/10000000000 : ℝ)] ![(16658357416621/50000000000000 : ℝ), (16020661627081/50000000000000 : ℝ), (34641961892713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870719023/2000000000 : ℝ)|^4207 ≤ (16658357416621/50000000000000 : ℝ)^3183
        have hw : |(870719023/2000000000 : ℝ)|=(870719023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113452197/5000000000 : ℝ)|^4207 ≤ (16020661627081/50000000000000 : ℝ)^3183
        have hw : |(2113452197/5000000000 : ℝ)|=(2113452197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483993857/10000000000 : ℝ)|^4207 ≤ (34641961892713/100000000000000 : ℝ)^3183
        have hw : |(4483993857/10000000000 : ℝ)|=(4483993857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s5_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129558693/10000000000 : ℝ)*x 0 + (2632999139/5000000000 : ℝ)*x 1 + (1348148123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129558693/10000000000 : ℝ)^4207 ≤ (12947749374791/100000000000000 : ℝ)^3183 := by
    have hnat : (2129558693 : ℕ)^4207*100000000000000^3183 ≤ 12947749374791^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129558693 10000000000 12947749374791 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632999139/5000000000 : ℝ)^4207 ≤ (10710716838029/25000000000000 : ℝ)^3183 := by
    have hnat : (2632999139 : ℕ)^4207*25000000000000^3183 ≤ 10710716838029^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632999139 5000000000 10710716838029 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348148123/2500000000 : ℝ)^4207 ≤ (44209383261907/100000000000000 : ℝ)^3183 := by
    have hnat : (1348148123 : ℕ)^4207*100000000000000^3183 ≤ 44209383261907^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348148123 2500000000 44209383261907 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129558693/10000000000 : ℝ), (2632999139/5000000000 : ℝ), (1348148123/2500000000 : ℝ)] ![(12947749374791/100000000000000 : ℝ), (10710716838029/25000000000000 : ℝ), (44209383261907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129558693/10000000000 : ℝ)|^4207 ≤ (12947749374791/100000000000000 : ℝ)^3183
        have hw : |(-2129558693/10000000000 : ℝ)|=(2129558693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632999139/5000000000 : ℝ)|^4207 ≤ (10710716838029/25000000000000 : ℝ)^3183
        have hw : |(2632999139/5000000000 : ℝ)|=(2632999139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348148123/2500000000 : ℝ)|^4207 ≤ (44209383261907/100000000000000 : ℝ)^3183
        have hw : |(1348148123/2500000000 : ℝ)|=(1348148123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s5_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265616631/500000000 : ℝ)*x 0 + (-2067174617/10000000000 : ℝ)*x 1 + (5392592439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265616631/500000000 : ℝ)^4207 ≤ (43341808940953/100000000000000 : ℝ)^3183 := by
    have hnat : (265616631 : ℕ)^4207*100000000000000^3183 ≤ 43341808940953^3183*500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265616631 500000000 43341808940953 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067174617/10000000000 : ℝ)^4207 ≤ (311220208833/2500000000000 : ℝ)^3183 := by
    have hnat : (2067174617 : ℕ)^4207*2500000000000^3183 ≤ 311220208833^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067174617 10000000000 311220208833 2500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392592439/10000000000 : ℝ)^4207 ≤ (2210469134381/5000000000000 : ℝ)^3183 := by
    have hnat : (5392592439 : ℕ)^4207*5000000000000^3183 ≤ 2210469134381^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392592439 10000000000 2210469134381 5000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265616631/500000000 : ℝ), (-2067174617/10000000000 : ℝ), (5392592439/10000000000 : ℝ)] ![(43341808940953/100000000000000 : ℝ), (311220208833/2500000000000 : ℝ), (2210469134381/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265616631/500000000 : ℝ)|^4207 ≤ (43341808940953/100000000000000 : ℝ)^3183
        have hw : |(265616631/500000000 : ℝ)|=(265616631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067174617/10000000000 : ℝ)|^4207 ≤ (311220208833/2500000000000 : ℝ)^3183
        have hw : |(-2067174617/10000000000 : ℝ)|=(2067174617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392592439/10000000000 : ℝ)|^4207 ≤ (2210469134381/5000000000000 : ℝ)^3183
        have hw : |(5392592439/10000000000 : ℝ)|=(5392592439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s5_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312332419/10000000000 : ℝ)*x 0 + (5392592679/10000000000 : ℝ)*x 1 + (-2067174563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312332419/10000000000 : ℝ)^4207 ≤ (43341806773479/100000000000000 : ℝ)^3183 := by
    have hnat : (5312332419 : ℕ)^4207*100000000000000^3183 ≤ 43341806773479^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312332419 10000000000 43341806773479 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392592679/10000000000 : ℝ)^4207 ≤ (44209385288163/100000000000000 : ℝ)^3183 := by
    have hnat : (5392592679 : ℕ)^4207*100000000000000^3183 ≤ 44209385288163^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392592679 10000000000 44209385288163 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067174563/10000000000 : ℝ)^4207 ≤ (12448807923507/100000000000000 : ℝ)^3183 := by
    have hnat : (2067174563 : ℕ)^4207*100000000000000^3183 ≤ 12448807923507^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067174563 10000000000 12448807923507 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312332419/10000000000 : ℝ), (5392592679/10000000000 : ℝ), (-2067174563/10000000000 : ℝ)] ![(43341806773479/100000000000000 : ℝ), (44209385288163/100000000000000 : ℝ), (12448807923507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312332419/10000000000 : ℝ)|^4207 ≤ (43341806773479/100000000000000 : ℝ)^3183
        have hw : |(5312332419/10000000000 : ℝ)|=(5312332419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392592679/10000000000 : ℝ)|^4207 ≤ (44209385288163/100000000000000 : ℝ)^3183
        have hw : |(5392592679/10000000000 : ℝ)|=(5392592679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067174563/10000000000 : ℝ)|^4207 ≤ (12448807923507/100000000000000 : ℝ)^3183
        have hw : |(-2067174563/10000000000 : ℝ)|=(2067174563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s5_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353605519/10000000000 : ℝ)*x 0 + (4483332563/10000000000 : ℝ)*x 1 + (2113783917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353605519/10000000000 : ℝ)^4207 ≤ (16658410032947/50000000000000 : ℝ)^3183 := by
    have hnat : (4353605519 : ℕ)^4207*50000000000000^3183 ≤ 16658410032947^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353605519 10000000000 16658410032947 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483332563/10000000000 : ℝ)^4207 ≤ (34635209501077/100000000000000 : ℝ)^3183 := by
    have hnat : (4483332563 : ℕ)^4207*100000000000000^3183 ≤ 34635209501077^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483332563 10000000000 34635209501077 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113783917/5000000000 : ℝ)^4207 ≤ (8011992604979/25000000000000 : ℝ)^3183 := by
    have hnat : (2113783917 : ℕ)^4207*25000000000000^3183 ≤ 8011992604979^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113783917 5000000000 8011992604979 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353605519/10000000000 : ℝ), (4483332563/10000000000 : ℝ), (2113783917/5000000000 : ℝ)] ![(16658410032947/50000000000000 : ℝ), (34635209501077/100000000000000 : ℝ), (8011992604979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353605519/10000000000 : ℝ)|^4207 ≤ (16658410032947/50000000000000 : ℝ)^3183
        have hw : |(4353605519/10000000000 : ℝ)|=(4353605519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483332563/10000000000 : ℝ)|^4207 ≤ (34635209501077/100000000000000 : ℝ)^3183
        have hw : |(4483332563/10000000000 : ℝ)|=(4483332563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113783917/5000000000 : ℝ)|^4207 ≤ (8011992604979/25000000000000 : ℝ)^3183
        have hw : |(2113783917/5000000000 : ℝ)|=(2113783917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5713/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7061/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11317/100000 : ℝ) ^ (8413/2048 : ℝ) ≤ (12966216295419671/100000000000000000000 : ℝ) := by
    have hpowers : (11317/100000 : ℝ)^8413 ≤ (12966216295419671/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11317 : ℕ)^8413*100000000000000000000^2048 ≤ 12966216295419671^2048*100000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11317 100000 12966216295419671 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11317/100000 : ℝ)) (X := (12966216295419671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8413/2048 : ℝ) ≤ (33280809550585113/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8413 ≤ (33280809550585113/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8413*100000000000000000000^2048 ≤ 33280809550585113^2048*25000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 33280809550585113 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (33280809550585113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012966216295419671/50000000000000000000 : ℝ) ≤ (10000631218504479/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50012966216295419671/50000000000000000000 : ℝ)^2048 ≤ (10000631218504479/10000000000000000 : ℝ)^8413 := by
      have hnat : (50012966216295419671 : ℕ)^2048*10000000000000000^8413 ≤ 10000631218504479^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012966216295419671 50000000000000000000 10000631218504479 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000631218504479/10000000000000000 : ℝ)) (X := (50012966216295419671/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252890439115375299/6250000000000000000 : ℝ) ≤ (625070350457403/625000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (6252890439115375299/6250000000000000000 : ℝ)^2048 ≤ (625070350457403/625000000000000 : ℝ)^8413 := by
      have hnat : (6252890439115375299 : ℕ)^2048*625000000000000^8413 ≤ 625070350457403^8413*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252890439115375299 6250000000000000000 625070350457403 625000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625070350457403/625000000000000 : ℝ)) (X := (6252890439115375299/6250000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033280809550585113/50000000000000000000 : ℝ) ≤ (10001619996132417/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50033280809550585113/50000000000000000000 : ℝ)^2048 ≤ (10001619996132417/10000000000000000 : ℝ)^8413 := by
      have hnat : (50033280809550585113 : ℕ)^2048*10000000000000000^8413 ≤ 10001619996132417^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033280809550585113 50000000000000000000 10001619996132417 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001619996132417/10000000000000000 : ℝ)) (X := (50033280809550585113/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12966216295419671/100000000000000000000 : ℝ) ≤ ((1945376835359946657/1946000000000000000 : ℝ)+2*(164796271323/97300000000000 : ℝ)*(11317/100000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (1945376835359946657/1946000000000000000 : ℝ)+2*(164796271323/97300000000000 : ℝ)*(11317/100000 : ℝ)=(10000631218504479/10000000000000000 : ℝ) by norm_num, show 1+2*(12966216295419671/100000000000000000000 : ℝ)=(50012966216295419671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33280809550585113/100000000000000000000 : ℝ)+(12966216295419671/100000000000000000000 : ℝ) ≤ ((1945376835359946657/1946000000000000000 : ℝ)+(164796271323/97300000000000 : ℝ)*((3559/25000 : ℝ)+(11317/100000 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (1945376835359946657/1946000000000000000 : ℝ)+(164796271323/97300000000000 : ℝ)*((3559/25000 : ℝ)+(11317/100000 : ℝ))=(625070350457403/625000000000000 : ℝ) by norm_num, show 1+(33280809550585113/100000000000000000000 : ℝ)+(12966216295419671/100000000000000000000 : ℝ)=(6252890439115375299/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33280809550585113/100000000000000000000 : ℝ) ≤ ((1945376835359946657/1946000000000000000 : ℝ)+2*(164796271323/97300000000000 : ℝ)*(3559/25000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (1945376835359946657/1946000000000000000 : ℝ)+2*(164796271323/97300000000000 : ℝ)*(3559/25000 : ℝ)=(10001619996132417/10000000000000000 : ℝ) by norm_num, show 1+2*(33280809550585113/100000000000000000000 : ℝ)=(50033280809550585113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1945376835359946657/1946000000000000000 : ℝ)*(X 1 0+X 2 0)+(164796271323/97300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1945376835359946657/1946000000000000000 : ℝ)) (alpha := (164796271323/97300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1945376835359946657/1946000000000000000 : ℝ)*(X 0 1+X 2 1)+(164796271323/97300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1945376835359946657/1946000000000000000 : ℝ)) (alpha := (164796271323/97300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1945376835359946657/1946000000000000000 : ℝ)*(X 0 2+X 1 2)+(164796271323/97300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (1945376835359946657/1946000000000000000 : ℝ)) (alpha := (164796271323/97300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-133097103/625000000 : ℝ)*X 0 0+(5392921117/10000000000 : ℝ)*X 0 1+(1053134179/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344754103/10000000000 : ℝ)*X 1 0+(-2194096353/10000000000 : ℝ)*X 1 1+(5265670903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83511783/156250000 : ℝ)*X 2 0+(5265670943/10000000000 : ℝ)*X 2 1+(-2194096287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870719023/2000000000 : ℝ)*X 0 0+(2113452197/5000000000 : ℝ)*X 0 1+(4483993857/10000000000 : ℝ)*X 0 2+(870719023/2000000000 : ℝ)*X 1 0+(2113452197/5000000000 : ℝ)*X 1 1+(4483993857/10000000000 : ℝ)*X 1 2+(870719023/2000000000 : ℝ)*X 2 0+(2113452197/5000000000 : ℝ)*X 2 1+(4483993857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2129558693/10000000000 : ℝ)*X 0 0+(2632999139/5000000000 : ℝ)*X 0 1+(1348148123/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265616631/500000000 : ℝ)*X 1 0+(-2067174617/10000000000 : ℝ)*X 1 1+(5392592439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312332419/10000000000 : ℝ)*X 2 0+(5392592679/10000000000 : ℝ)*X 2 1+(-2067174563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353605519/10000000000 : ℝ)*X 0 0+(4483332563/10000000000 : ℝ)*X 0 1+(2113783917/5000000000 : ℝ)*X 0 2+(4353605519/10000000000 : ℝ)*X 1 0+(4483332563/10000000000 : ℝ)*X 1 1+(2113783917/5000000000 : ℝ)*X 1 2+(4353605519/10000000000 : ℝ)*X 2 0+(4483332563/10000000000 : ℝ)*X 2 1+(2113783917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144875900691267924828311031/24325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (607866381/50000000000000 : ℝ)*(base19) + (606538189/50000000000000 : ℝ)*(base23) + (4246259/50000000000000 : ℝ)*(lower2) + (70573603/100000000000000 : ℝ)*(upper3) + (20834589/12500000000000 : ℝ)*(upper5) + (1468542166761861/25000000000000 : ℝ)*(major0) + (1468542166761861/25000000000000 : ℝ)*(major1) + (1468542166761861/25000000000000 : ℝ)*(major2) + (392928367685191/5000000000000 : ℝ)*(sp0) + (1571721284240133/20000000000000 : ℝ)*(sp1) + (7858606423857049/100000000000000 : ℝ)*(sp2) + (243107116312297/6250000000000 : ℝ)*(sp3) + (20141614803/50000000000000 : ℝ)*(sp4) + (15637636573/100000000000000 : ℝ)*(sp7) + (1944864749316663/50000000000000 : ℝ)*(f.failure) + (3929303818466713/50000000000000 : ℝ)*(f.sum) + (31617987097527/4865000000000000000000000000 : ℝ)*base65 + (222792983727641323/48650000000000000000000000000000 : ℝ)*base68 + (148136742038591323/48650000000000000000000000000000 : ℝ)*base70 + (566605018137191323/48650000000000000000000000000000 : ℝ)*base72 + (15129918378791/2432500000000000000000000000 : ℝ)*base73 + (252607248959458677/48650000000000000000000000000000 : ℝ)*base75 + (425415760846641323/48650000000000000000000000000000 : ℝ)*base78 + (342089862751008677/48650000000000000000000000000000 : ℝ)*base79 + (16391725451617/4865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (272961/78125000000000000000 : ℝ)*base89 + (272961/78125000000000000000 : ℝ)*base91 + (272961/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128922893890056694398357873/13900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61583609/2500000000000 : ℝ)*(base19) + (2453682959/100000000000000 : ℝ)*(base23) + (19854689/6250000000000 : ℝ)*(upper3) + (4580613/4000000000000 : ℝ)*(lower4) + (52162659/25000000000000 : ℝ)*(upper5) + (5904543731688447/100000000000000 : ℝ)*(major0) + (5904543731688447/100000000000000 : ℝ)*(major1) + (5904543731688447/100000000000000 : ℝ)*(major2) + (61094606229/100000000000000 : ℝ)*(sp1) + (73162356523/100000000000000 : ℝ)*(sp2) + (7899244037521393/100000000000000 : ℝ)*(sp4) + (1579836095914161/20000000000000 : ℝ)*(sp5) + (987396052685239/12500000000000 : ℝ)*(sp6) + (3909843116687877/100000000000000 : ℝ)*(sp7) + (3909843116687877/100000000000000 : ℝ)*(f.failure) + (7899244037521393/100000000000000 : ℝ)*(f.sum) + (4654571099729/4865000000000000000000000000 : ℝ)*base66 + (1664814384402208321/194600000000000000000000000000000 : ℝ)*base68 + (3430970857449608321/194600000000000000000000000000000 : ℝ)*base70 + (3709021190239208321/194600000000000000000000000000000 : ℝ)*base72 + (4121245967963/608125000000000000000000000 : ℝ)*base74 + (2869514211789208321/194600000000000000000000000000000 : ℝ)*base76 + (2237010554147408321/194600000000000000000000000000000 : ℝ)*base78 + (4899761531214008321/194600000000000000000000000000000 : ℝ)*base80 + (13164873881/76015625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (461919/156250000000000000000 : ℝ)*base89 + (461919/156250000000000000000 : ℝ)*base91 + (461919/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1221_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1221_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1221_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1221_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1221_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
