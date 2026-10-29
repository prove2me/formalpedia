-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1367_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:36.839586+00:00
-- url     : https://prove2.me/submissions/4c18735b-384d-4ebe-bd8a-86d793aa55f3

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
theorem support_rectangle_w1367_s6_0 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-505641703/2500000000 : ℝ)*x 0 + (5411426807/10000000000 : ℝ)*x 1 + (1311333921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505641703/2500000000 : ℝ)^4327 ≤ (12323045685767/100000000000000 : ℝ)^3303 := by
    have hnat : (505641703 : ℕ)^4327*100000000000000^3303 ≤ 12323045685767^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505641703 2500000000 12323045685767 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411426807/10000000000 : ℝ)^4327 ≤ (8946698189871/20000000000000 : ℝ)^3303 := by
    have hnat : (5411426807 : ℕ)^4327*20000000000000^3303 ≤ 8946698189871^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411426807 10000000000 8946698189871 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311333921/2500000000 : ℝ)^4327 ≤ (10735865836829/25000000000000 : ℝ)^3303 := by
    have hnat : (1311333921 : ℕ)^4327*25000000000000^3303 ≤ 10735865836829^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311333921 2500000000 10735865836829 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505641703/2500000000 : ℝ), (5411426807/10000000000 : ℝ), (1311333921/2500000000 : ℝ)] ![(12323045685767/100000000000000 : ℝ), (8946698189871/20000000000000 : ℝ), (10735865836829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505641703/2500000000 : ℝ)|^4327 ≤ (12323045685767/100000000000000 : ℝ)^3303
        have hw : |(-505641703/2500000000 : ℝ)|=(505641703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411426807/10000000000 : ℝ)|^4327 ≤ (8946698189871/20000000000000 : ℝ)^3303
        have hw : |(5411426807/10000000000 : ℝ)|=(5411426807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311333921/2500000000 : ℝ)|^4327 ≤ (10735865836829/25000000000000 : ℝ)^3303
        have hw : |(1311333921/2500000000 : ℝ)|=(1311333921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s6_1 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348554777/10000000000 : ℝ)*x 0 + (-2107172157/10000000000 : ℝ)*x 1 + (5245335689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348554777/10000000000 : ℝ)^4327 ≤ (44053862038079/100000000000000 : ℝ)^3303 := by
    have hnat : (5348554777 : ℕ)^4327*100000000000000^3303 ≤ 44053862038079^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348554777 10000000000 44053862038079 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107172157/10000000000 : ℝ)^4327 ≤ (13002674544247/100000000000000 : ℝ)^3303 := by
    have hnat : (2107172157 : ℕ)^4327*100000000000000^3303 ≤ 13002674544247^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107172157 10000000000 13002674544247 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245335689/10000000000 : ℝ)^4327 ≤ (21471731700471/50000000000000 : ℝ)^3303 := by
    have hnat : (5245335689 : ℕ)^4327*50000000000000^3303 ≤ 21471731700471^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245335689 10000000000 21471731700471 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348554777/10000000000 : ℝ), (-2107172157/10000000000 : ℝ), (5245335689/10000000000 : ℝ)] ![(44053862038079/100000000000000 : ℝ), (13002674544247/100000000000000 : ℝ), (21471731700471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348554777/10000000000 : ℝ)|^4327 ≤ (44053862038079/100000000000000 : ℝ)^3303
        have hw : |(5348554777/10000000000 : ℝ)|=(5348554777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107172157/10000000000 : ℝ)|^4327 ≤ (13002674544247/100000000000000 : ℝ)^3303
        have hw : |(-2107172157/10000000000 : ℝ)|=(2107172157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245335689/10000000000 : ℝ)|^4327 ≤ (21471731700471/50000000000000 : ℝ)^3303
        have hw : |(5245335689/10000000000 : ℝ)|=(5245335689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s6_2 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348554779/10000000000 : ℝ)*x 0 + (5245335683/10000000000 : ℝ)*x 1 + (-2107172163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348554779/10000000000 : ℝ)^4327 ≤ (44053862059659/100000000000000 : ℝ)^3303 := by
    have hnat : (5348554779 : ℕ)^4327*100000000000000^3303 ≤ 44053862059659^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348554779 10000000000 44053862059659 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245335683/10000000000 : ℝ)^4327 ≤ (42943463336591/100000000000000 : ℝ)^3303 := by
    have hnat : (5245335683 : ℕ)^4327*100000000000000^3303 ≤ 42943463336591^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245335683 10000000000 42943463336591 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107172163/10000000000 : ℝ)^4327 ≤ (13002674592749/100000000000000 : ℝ)^3303 := by
    have hnat : (2107172163 : ℕ)^4327*100000000000000^3303 ≤ 13002674592749^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107172163 10000000000 13002674592749 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348554779/10000000000 : ℝ), (5245335683/10000000000 : ℝ), (-2107172163/10000000000 : ℝ)] ![(44053862059659/100000000000000 : ℝ), (42943463336591/100000000000000 : ℝ), (13002674592749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348554779/10000000000 : ℝ)|^4327 ≤ (44053862059659/100000000000000 : ℝ)^3303
        have hw : |(5348554779/10000000000 : ℝ)|=(5348554779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245335683/10000000000 : ℝ)|^4327 ≤ (42943463336591/100000000000000 : ℝ)^3303
        have hw : |(5245335683/10000000000 : ℝ)|=(5245335683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107172163/10000000000 : ℝ)|^4327 ≤ (13002674592749/100000000000000 : ℝ)^3303
        have hw : |(-2107172163/10000000000 : ℝ)|=(2107172163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s6_3 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320123619/10000000000 : ℝ)*x 0 + (4147838969/10000000000 : ℝ)*x 1 + (4499003927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320123619/10000000000 : ℝ)^4327 ≤ (33303682941549/100000000000000 : ℝ)^3303 := by
    have hnat : (4320123619 : ℕ)^4327*100000000000000^3303 ≤ 33303682941549^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320123619 10000000000 33303682941549 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4147838969/10000000000 : ℝ)^4327 ≤ (7893663008829/25000000000000 : ℝ)^3303 := by
    have hnat : (4147838969 : ℕ)^4327*25000000000000^3303 ≤ 7893663008829^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147838969 10000000000 7893663008829 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499003927/10000000000 : ℝ)^4327 ≤ (35121665001821/100000000000000 : ℝ)^3303 := by
    have hnat : (4499003927 : ℕ)^4327*100000000000000^3303 ≤ 35121665001821^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499003927 10000000000 35121665001821 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320123619/10000000000 : ℝ), (4147838969/10000000000 : ℝ), (4499003927/10000000000 : ℝ)] ![(33303682941549/100000000000000 : ℝ), (7893663008829/25000000000000 : ℝ), (35121665001821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320123619/10000000000 : ℝ)|^4327 ≤ (33303682941549/100000000000000 : ℝ)^3303
        have hw : |(4320123619/10000000000 : ℝ)|=(4320123619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4147838969/10000000000 : ℝ)|^4327 ≤ (7893663008829/25000000000000 : ℝ)^3303
        have hw : |(4147838969/10000000000 : ℝ)|=(4147838969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499003927/10000000000 : ℝ)|^4327 ≤ (35121665001821/100000000000000 : ℝ)^3303
        have hw : |(4499003927/10000000000 : ℝ)|=(4499003927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s6_4 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-252822343/1250000000 : ℝ)*x 0 + (5245931589/10000000000 : ℝ)*x 1 + (5410827819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252822343/1250000000 : ℝ)^4327 ≤ (12323140923083/100000000000000 : ℝ)^3303 := by
    have hnat : (252822343 : ℕ)^4327*100000000000000^3303 ≤ 12323140923083^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252822343 1250000000 12323140923083 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245931589/10000000000 : ℝ)^4327 ≤ (42949854611637/100000000000000 : ℝ)^3303 := by
    have hnat : (5245931589 : ℕ)^4327*100000000000000^3303 ≤ 42949854611637^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245931589 10000000000 42949854611637 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410827819/10000000000 : ℝ)^4327 ≤ (5590875556969/12500000000000 : ℝ)^3303 := by
    have hnat : (5410827819 : ℕ)^4327*12500000000000^3303 ≤ 5590875556969^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410827819 10000000000 5590875556969 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-252822343/1250000000 : ℝ), (5245931589/10000000000 : ℝ), (5410827819/10000000000 : ℝ)] ![(12323140923083/100000000000000 : ℝ), (42949854611637/100000000000000 : ℝ), (5590875556969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-252822343/1250000000 : ℝ)|^4327 ≤ (12323140923083/100000000000000 : ℝ)^3303
        have hw : |(-252822343/1250000000 : ℝ)|=(252822343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245931589/10000000000 : ℝ)|^4327 ≤ (42949854611637/100000000000000 : ℝ)^3303
        have hw : |(5245931589/10000000000 : ℝ)|=(5245931589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410827819/10000000000 : ℝ)|^4327 ≤ (5590875556969/12500000000000 : ℝ)^3303
        have hw : |(5410827819/10000000000 : ℝ)|=(5410827819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s6_5 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530565277/1000000000 : ℝ)*x 0 + (-485420007/2500000000 : ℝ)*x 1 + (5410827821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530565277/1000000000 : ℝ)^4327 ≤ (43591521321153/100000000000000 : ℝ)^3303 := by
    have hnat : (530565277 : ℕ)^4327*100000000000000^3303 ≤ 43591521321153^3303*1000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530565277 1000000000 43591521321153 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485420007/2500000000 : ℝ)^4327 ≤ (11681474187323/100000000000000 : ℝ)^3303 := by
    have hnat : (485420007 : ℕ)^4327*100000000000000^3303 ≤ 11681474187323^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485420007 2500000000 11681474187323 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410827821/10000000000 : ℝ)^4327 ≤ (4472700447741/10000000000000 : ℝ)^3303 := by
    have hnat : (5410827821 : ℕ)^4327*10000000000000^3303 ≤ 4472700447741^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410827821 10000000000 4472700447741 10000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530565277/1000000000 : ℝ), (-485420007/2500000000 : ℝ), (5410827821/10000000000 : ℝ)] ![(43591521321153/100000000000000 : ℝ), (11681474187323/100000000000000 : ℝ), (4472700447741/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530565277/1000000000 : ℝ)|^4327 ≤ (43591521321153/100000000000000 : ℝ)^3303
        have hw : |(530565277/1000000000 : ℝ)|=(530565277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-485420007/2500000000 : ℝ)|^4327 ≤ (11681474187323/100000000000000 : ℝ)^3303
        have hw : |(-485420007/2500000000 : ℝ)|=(485420007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410827821/10000000000 : ℝ)|^4327 ≤ (4472700447741/10000000000000 : ℝ)^3303
        have hw : |(5410827821/10000000000 : ℝ)|=(5410827821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s6_6 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305652769/10000000000 : ℝ)*x 0 + (2705413911/5000000000 : ℝ)*x 1 + (-1941680029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305652769/10000000000 : ℝ)^4327 ≤ (43591521310389/100000000000000 : ℝ)^3303 := by
    have hnat : (5305652769 : ℕ)^4327*100000000000000^3303 ≤ 43591521310389^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305652769 10000000000 43591521310389 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705413911/5000000000 : ℝ)^4327 ≤ (44727004488239/100000000000000 : ℝ)^3303 := by
    have hnat : (2705413911 : ℕ)^4327*100000000000000^3303 ≤ 44727004488239^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705413911 5000000000 44727004488239 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1941680029/10000000000 : ℝ)^4327 ≤ (2920368548801/25000000000000 : ℝ)^3303 := by
    have hnat : (1941680029 : ℕ)^4327*25000000000000^3303 ≤ 2920368548801^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941680029 10000000000 2920368548801 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305652769/10000000000 : ℝ), (2705413911/5000000000 : ℝ), (-1941680029/10000000000 : ℝ)] ![(43591521310389/100000000000000 : ℝ), (44727004488239/100000000000000 : ℝ), (2920368548801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305652769/10000000000 : ℝ)|^4327 ≤ (43591521310389/100000000000000 : ℝ)^3303
        have hw : |(5305652769/10000000000 : ℝ)|=(5305652769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705413911/5000000000 : ℝ)|^4327 ≤ (44727004488239/100000000000000 : ℝ)^3303
        have hw : |(2705413911/5000000000 : ℝ)|=(2705413911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1941680029/10000000000 : ℝ)|^4327 ≤ (2920368548801/25000000000000 : ℝ)^3303
        have hw : |(-1941680029/10000000000 : ℝ)|=(1941680029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s6_7 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320148827/10000000000 : ℝ)*x 0 + (4497744003/10000000000 : ℝ)*x 1 + (4149105397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320148827/10000000000 : ℝ)^4327 ≤ (33303937515049/100000000000000 : ℝ)^3303 := by
    have hnat : (4320148827 : ℕ)^4327*100000000000000^3303 ≤ 33303937515049^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320148827 10000000000 33303937515049 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497744003/10000000000 : ℝ)^4327 ≤ (17554390325523/50000000000000 : ℝ)^3303 := by
    have hnat : (4497744003 : ℕ)^4327*50000000000000^3303 ≤ 17554390325523^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497744003 10000000000 17554390325523 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149105397/10000000000 : ℝ)^4327 ≤ (31587281823401/100000000000000 : ℝ)^3303 := by
    have hnat : (4149105397 : ℕ)^4327*100000000000000^3303 ≤ 31587281823401^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149105397 10000000000 31587281823401 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320148827/10000000000 : ℝ), (4497744003/10000000000 : ℝ), (4149105397/10000000000 : ℝ)] ![(33303937515049/100000000000000 : ℝ), (17554390325523/50000000000000 : ℝ), (31587281823401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320148827/10000000000 : ℝ)|^4327 ≤ (33303937515049/100000000000000 : ℝ)^3303
        have hw : |(4320148827/10000000000 : ℝ)|=(4320148827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497744003/10000000000 : ℝ)|^4327 ≤ (17554390325523/50000000000000 : ℝ)^3303
        have hw : |(4497744003/10000000000 : ℝ)|=(4497744003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149105397/10000000000 : ℝ)|^4327 ≤ (31587281823401/100000000000000 : ℝ)^3303
        have hw : |(4149105397/10000000000 : ℝ)|=(4149105397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1367_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    (5603/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14723/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (14/125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (14/125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (14/125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (14/125 : ℝ) ^ (2163/512 : ℝ) ≤ (2405789104346533/25000000000000000000 : ℝ) := by
    have hpowers : (14/125 : ℝ)^2163 ≤ (2405789104346533/25000000000000000000 : ℝ)^512 := by
      have hnat : (14 : ℕ)^2163*25000000000000000000^512 ≤ 2405789104346533^512*125^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14 125 2405789104346533 25000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14/125 : ℝ)) (X := (2405789104346533/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14729/100000 : ℝ) ^ (2163/512 : ℝ) ≤ (15304775706058019/50000000000000000000 : ℝ) := by
    have hpowers : (14729/100000 : ℝ)^2163 ≤ (15304775706058019/50000000000000000000 : ℝ)^512 := by
      have hnat : (14729 : ℕ)^2163*50000000000000000000^512 ≤ 15304775706058019^512*100000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14729 100000 15304775706058019 50000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14729/100000 : ℝ)) (X := (15304775706058019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502405789104346533/12500000000000000000 : ℝ) ≤ (1000045554269263/1000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (12502405789104346533/12500000000000000000 : ℝ)^512 ≤ (1000045554269263/1000000000000000 : ℝ)^2163 := by
      have hnat : (12502405789104346533 : ℕ)^512*1000000000000000^2163 ≤ 1000045554269263^2163*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502405789104346533 12500000000000000000 1000045554269263 1000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000045554269263/1000000000000000 : ℝ)) (X := (12502405789104346533/12500000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004023270782950217/10000000000000000000 : ℝ) ≤ (10000952195294977/10000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (10004023270782950217/10000000000000000000 : ℝ)^512 ≤ (10000952195294977/10000000000000000 : ℝ)^2163 := by
      have hnat : (10004023270782950217 : ℕ)^512*10000000000000000^2163 ≤ 10000952195294977^2163*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004023270782950217 10000000000000000000 10000952195294977 10000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000952195294977/10000000000000000 : ℝ)) (X := (10004023270782950217/10000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015304775706058019/25000000000000000000 : ℝ) ≤ (2500362211974331/2500000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (25015304775706058019/25000000000000000000 : ℝ)^512 ≤ (2500362211974331/2500000000000000 : ℝ)^2163 := by
      have hnat : (25015304775706058019 : ℕ)^512*2500000000000000^2163 ≤ 2500362211974331^2163*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015304775706058019 25000000000000000000 2500362211974331 2500000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500362211974331/2500000000000000 : ℝ)) (X := (25015304775706058019/25000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2405789104346533/25000000000000000000 : ℝ) ≤ ((3528048259186971847/3529000000000000000 : ℝ)+2*(496652602347/352900000000000 : ℝ)*(14/125 : ℝ))^(2163/512 : ℝ) := by
    rw [show (3528048259186971847/3529000000000000000 : ℝ)+2*(496652602347/352900000000000 : ℝ)*(14/125 : ℝ)=(1000045554269263/1000000000000000 : ℝ) by norm_num, show 1+2*(2405789104346533/25000000000000000000 : ℝ)=(12502405789104346533/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15304775706058019/50000000000000000000 : ℝ)+(2405789104346533/25000000000000000000 : ℝ) ≤ ((3528048259186971847/3529000000000000000 : ℝ)+(496652602347/352900000000000 : ℝ)*((14729/100000 : ℝ)+(14/125 : ℝ)))^(2163/512 : ℝ) := by
    rw [show (3528048259186971847/3529000000000000000 : ℝ)+(496652602347/352900000000000 : ℝ)*((14729/100000 : ℝ)+(14/125 : ℝ))=(10000952195294977/10000000000000000 : ℝ) by norm_num, show 1+(15304775706058019/50000000000000000000 : ℝ)+(2405789104346533/25000000000000000000 : ℝ)=(10004023270782950217/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15304775706058019/50000000000000000000 : ℝ) ≤ ((3528048259186971847/3529000000000000000 : ℝ)+2*(496652602347/352900000000000 : ℝ)*(14729/100000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (3528048259186971847/3529000000000000000 : ℝ)+2*(496652602347/352900000000000 : ℝ)*(14729/100000 : ℝ)=(2500362211974331/2500000000000000 : ℝ) by norm_num, show 1+2*(15304775706058019/50000000000000000000 : ℝ)=(25015304775706058019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3528048259186971847/3529000000000000000 : ℝ)*(X 1 0+X 2 0)+(496652602347/352900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (14/125 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (3528048259186971847/3529000000000000000 : ℝ)) (alpha := (496652602347/352900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3528048259186971847/3529000000000000000 : ℝ)*(X 0 1+X 2 1)+(496652602347/352900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (14/125 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (3528048259186971847/3529000000000000000 : ℝ)) (alpha := (496652602347/352900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3528048259186971847/3529000000000000000 : ℝ)*(X 0 2+X 1 2)+(496652602347/352900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (14/125 : ℝ)) (hi := (14729/100000 : ℝ)) (c := (3528048259186971847/3529000000000000000 : ℝ)) (alpha := (496652602347/352900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-505641703/2500000000 : ℝ)*X 0 0+(5411426807/10000000000 : ℝ)*X 0 1+(1311333921/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348554777/10000000000 : ℝ)*X 1 0+(-2107172157/10000000000 : ℝ)*X 1 1+(5245335689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348554779/10000000000 : ℝ)*X 2 0+(5245335683/10000000000 : ℝ)*X 2 1+(-2107172163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320123619/10000000000 : ℝ)*X 0 0+(4147838969/10000000000 : ℝ)*X 0 1+(4499003927/10000000000 : ℝ)*X 0 2+(4320123619/10000000000 : ℝ)*X 1 0+(4147838969/10000000000 : ℝ)*X 1 1+(4499003927/10000000000 : ℝ)*X 1 2+(4320123619/10000000000 : ℝ)*X 2 0+(4147838969/10000000000 : ℝ)*X 2 1+(4499003927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-252822343/1250000000 : ℝ)*X 0 0+(5245931589/10000000000 : ℝ)*X 0 1+(5410827819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530565277/1000000000 : ℝ)*X 1 0+(-485420007/2500000000 : ℝ)*X 1 1+(5410827821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305652769/10000000000 : ℝ)*X 2 0+(2705413911/5000000000 : ℝ)*X 2 1+(-1941680029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320148827/10000000000 : ℝ)*X 0 0+(4497744003/10000000000 : ℝ)*X 0 1+(4149105397/10000000000 : ℝ)*X 0 2+(4320148827/10000000000 : ℝ)*X 1 0+(4497744003/10000000000 : ℝ)*X 1 1+(4149105397/10000000000 : ℝ)*X 1 2+(4320148827/10000000000 : ℝ)*X 2 0+(4497744003/10000000000 : ℝ)*X 2 1+(4149105397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (814485772857946244192300127/88225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1725173883/100000000000000 : ℝ)*(base19) + (798714221/50000000000000 : ℝ)*(base23) + (69529521/100000000000000 : ℝ)*(lower2) + (238720163/100000000000000 : ℝ)*(upper3) + (68290807/50000000000000 : ℝ)*(upper5) + (2217140846417751/50000000000000 : ℝ)*(major0) + (2217140846417751/50000000000000 : ℝ)*(major1) + (2217140846417751/50000000000000 : ℝ)*(major2) + (3010414356552941/50000000000000 : ℝ)*(sp0) + (752607788750707/12500000000000 : ℝ)*(sp1) + (752607804718887/12500000000000 : ℝ)*(sp2) + (1423840353931831/50000000000000 : ℝ)*(sp3) + (7064414731/20000000000000 : ℝ)*(sp4) + (18334897263/100000000000000 : ℝ)*(sp7) + (113907961710437/4000000000000 : ℝ)*(f.failure) + (3010432017589769/50000000000000 : ℝ)*(f.sum) + (121348586226681/17645000000000000000000000000 : ℝ)*base66 + (3164987355041826097/176450000000000000000000000000000 : ℝ)*base67 + (2063047227017926097/176450000000000000000000000000000 : ℝ)*base69 + (1415284954042076097/176450000000000000000000000000000 : ℝ)*base71 + (103556833510819/17645000000000000000000000000 : ℝ)*base73 + (185133062978976097/176450000000000000000000000000000 : ℝ)*base75 + (1728048036287676097/176450000000000000000000000000000 : ℝ)*base77 + (996806456818276097/176450000000000000000000000000000 : ℝ)*base79 + (94635338347671/17645000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (915631/100000000000000000000 : ℝ)*base90 + (915631/100000000000000000000 : ℝ)*base92 + (915631/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (710401020158199314766675003/88225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13927969/1000000000000 : ℝ)*(base19) + (757290283/50000000000000 : ℝ)*(base23) + (165276537/100000000000000 : ℝ)*(upper3) + (55968413/100000000000000 : ℝ)*(lower4) + (167489337/100000000000000 : ℝ)*(upper5) + (2233179604566183/50000000000000 : ℝ)*(major0) + (2233179604566183/50000000000000 : ℝ)*(major1) + (2233179604566183/50000000000000 : ℝ)*(major2) + (14354604643/50000000000000 : ℝ)*(sp1) + (1543289967/5000000000000 : ℝ)*(sp2) + (1212883780394831/20000000000000 : ℝ)*(sp4) + (189512149998999/3125000000000 : ℝ)*(sp5) + (758048315199281/12500000000000 : ℝ)*(sp6) + (2868299247885539/100000000000000 : ℝ)*(sp7) + (2868299247885539/100000000000000 : ℝ)*(f.failure) + (1212883780394831/20000000000000 : ℝ)*(f.sum) + (15241373772283/17645000000000000000000000000 : ℝ)*base66 + (757326177038139999/176450000000000000000000000000000 : ℝ)*base68 + (1532368159511339999/176450000000000000000000000000000 : ℝ)*base70 + (459616225723510001/176450000000000000000000000000000 : ℝ)*base71 + (19756986526907/17645000000000000000000000000 : ℝ)*base73 + (490647561349989999/176450000000000000000000000000000 : ℝ)*base76 + (115682004888010001/176450000000000000000000000000000 : ℝ)*base77 + (601579899145589999/176450000000000000000000000000000 : ℝ)*base80 + (53084355056707/17645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15280343/2500000000000000000000 : ℝ)*base89 + (15280343/2500000000000000000000 : ℝ)*base91 + (15280343/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1367_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1367_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1367_s7_0 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1011285691/5000000000 : ℝ)*x 0 + (1082275833/2000000000 : ℝ)*x 1 + (1311345097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011285691/5000000000 : ℝ)^4327 ≤ (1232308216199/10000000000000 : ℝ)^3303 := by
    have hnat : (1011285691 : ℕ)^4327*10000000000000^3303 ≤ 1232308216199^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011285691 5000000000 1232308216199 10000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082275833/2000000000 : ℝ)^4327 ≤ (44732975021809/100000000000000 : ℝ)^3303 := by
    have hnat : (1082275833 : ℕ)^4327*100000000000000^3303 ≤ 44732975021809^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082275833 2000000000 44732975021809 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311345097/2500000000 : ℝ)^4327 ≤ (858878856073/2000000000000 : ℝ)^3303 := by
    have hnat : (1311345097 : ℕ)^4327*2000000000000^3303 ≤ 858878856073^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311345097 2500000000 858878856073 2000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1011285691/5000000000 : ℝ), (1082275833/2000000000 : ℝ), (1311345097/2500000000 : ℝ)] ![(1232308216199/10000000000000 : ℝ), (44732975021809/100000000000000 : ℝ), (858878856073/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1011285691/5000000000 : ℝ)|^4327 ≤ (1232308216199/10000000000000 : ℝ)^3303
        have hw : |(-1011285691/5000000000 : ℝ)|=(1011285691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082275833/2000000000 : ℝ)|^4327 ≤ (44732975021809/100000000000000 : ℝ)^3303
        have hw : |(1082275833/2000000000 : ℝ)|=(1082275833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311345097/2500000000 : ℝ)|^4327 ≤ (858878856073/2000000000000 : ℝ)^3303
        have hw : |(1311345097/2500000000 : ℝ)|=(1311345097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s7_1 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348542801/10000000000 : ℝ)*x 0 + (-526782213/2500000000 : ℝ)*x 1 + (5245380377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348542801/10000000000 : ℝ)^4327 ≤ (4405373281577/10000000000000 : ℝ)^3303 := by
    have hnat : (5348542801 : ℕ)^4327*10000000000000^3303 ≤ 4405373281577^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348542801 10000000000 4405373281577 10000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526782213/2500000000 : ℝ)^4327 ≤ (13002324480083/100000000000000 : ℝ)^3303 := by
    have hnat : (526782213 : ℕ)^4327*100000000000000^3303 ≤ 13002324480083^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526782213 2500000000 13002324480083 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245380377/10000000000 : ℝ)^4327 ≤ (42943942685673/100000000000000 : ℝ)^3303 := by
    have hnat : (5245380377 : ℕ)^4327*100000000000000^3303 ≤ 42943942685673^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245380377 10000000000 42943942685673 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348542801/10000000000 : ℝ), (-526782213/2500000000 : ℝ), (5245380377/10000000000 : ℝ)] ![(4405373281577/10000000000000 : ℝ), (13002324480083/100000000000000 : ℝ), (42943942685673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348542801/10000000000 : ℝ)|^4327 ≤ (4405373281577/10000000000000 : ℝ)^3303
        have hw : |(5348542801/10000000000 : ℝ)|=(5348542801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-526782213/2500000000 : ℝ)|^4327 ≤ (13002324480083/100000000000000 : ℝ)^3303
        have hw : |(-526782213/2500000000 : ℝ)|=(526782213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245380377/10000000000 : ℝ)|^4327 ≤ (42943942685673/100000000000000 : ℝ)^3303
        have hw : |(5245380377/10000000000 : ℝ)|=(5245380377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s7_2 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267427141/500000000 : ℝ)*x 0 + (131134509/250000000 : ℝ)*x 1 + (-2107128849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267427141/500000000 : ℝ)^4327 ≤ (44053733020781/100000000000000 : ℝ)^3303 := by
    have hnat : (267427141 : ℕ)^4327*100000000000000^3303 ≤ 44053733020781^3303*500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267427141 500000000 44053733020781 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131134509/250000000 : ℝ)^4327 ≤ (21471971251673/50000000000000 : ℝ)^3303 := by
    have hnat : (131134509 : ℕ)^4327*50000000000000^3303 ≤ 21471971251673^3303*250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131134509 250000000 21471971251673 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107128849/10000000000 : ℝ)^4327 ≤ (1625290556979/12500000000000 : ℝ)^3303 := by
    have hnat : (2107128849 : ℕ)^4327*12500000000000^3303 ≤ 1625290556979^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107128849 10000000000 1625290556979 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267427141/500000000 : ℝ), (131134509/250000000 : ℝ), (-2107128849/10000000000 : ℝ)] ![(44053733020781/100000000000000 : ℝ), (21471971251673/50000000000000 : ℝ), (1625290556979/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267427141/500000000 : ℝ)|^4327 ≤ (44053733020781/100000000000000 : ℝ)^3303
        have hw : |(267427141/500000000 : ℝ)|=(267427141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131134509/250000000 : ℝ)|^4327 ≤ (21471971251673/50000000000000 : ℝ)^3303
        have hw : |(131134509/250000000 : ℝ)|=(131134509/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107128849/10000000000 : ℝ)|^4327 ≤ (1625290556979/12500000000000 : ℝ)^3303
        have hw : |(-2107128849/10000000000 : ℝ)|=(2107128849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s7_3 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172805073/400000000 : ℝ)*x 0 + (4147936199/10000000000 : ℝ)*x 1 + (4498905949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172805073/400000000 : ℝ)^4327 ≤ (33303715318651/100000000000000 : ℝ)^3303 := by
    have hnat : (172805073 : ℕ)^4327*100000000000000^3303 ≤ 33303715318651^3303*400000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172805073 400000000 33303715318651 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4147936199/10000000000 : ℝ)^4327 ≤ (7893905411209/25000000000000 : ℝ)^3303 := by
    have hnat : (4147936199 : ℕ)^4327*25000000000000^3303 ≤ 7893905411209^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147936199 10000000000 7893905411209 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498905949/10000000000 : ℝ)^4327 ≤ (17560331505031/50000000000000 : ℝ)^3303 := by
    have hnat : (4498905949 : ℕ)^4327*50000000000000^3303 ≤ 17560331505031^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498905949 10000000000 17560331505031 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172805073/400000000 : ℝ), (4147936199/10000000000 : ℝ), (4498905949/10000000000 : ℝ)] ![(33303715318651/100000000000000 : ℝ), (7893905411209/25000000000000 : ℝ), (17560331505031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172805073/400000000 : ℝ)|^4327 ≤ (33303715318651/100000000000000 : ℝ)^3303
        have hw : |(172805073/400000000 : ℝ)|=(172805073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4147936199/10000000000 : ℝ)|^4327 ≤ (7893905411209/25000000000000 : ℝ)^3303
        have hw : |(4147936199/10000000000 : ℝ)|=(4147936199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498905949/10000000000 : ℝ)|^4327 ≤ (17560331505031/50000000000000 : ℝ)^3303
        have hw : |(4498905949/10000000000 : ℝ)|=(4498905949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s7_4 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022583069/10000000000 : ℝ)*x 0 + (655747009/1250000000 : ℝ)*x 1 + (5410780573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022583069/10000000000 : ℝ)^4327 ≤ (12323175443859/100000000000000 : ℝ)^3303 := by
    have hnat : (2022583069 : ℕ)^4327*100000000000000^3303 ≤ 12323175443859^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022583069 10000000000 12323175443859 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655747009/1250000000 : ℝ)^4327 ≤ (8590066342903/20000000000000 : ℝ)^3303 := by
    have hnat : (655747009 : ℕ)^4327*20000000000000^3303 ≤ 8590066342903^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655747009 1250000000 8590066342903 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410780573/10000000000 : ℝ)^4327 ≤ (8945298566829/20000000000000 : ℝ)^3303 := by
    have hnat : (5410780573 : ℕ)^4327*20000000000000^3303 ≤ 8945298566829^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410780573 10000000000 8945298566829 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022583069/10000000000 : ℝ), (655747009/1250000000 : ℝ), (5410780573/10000000000 : ℝ)] ![(12323175443859/100000000000000 : ℝ), (8590066342903/20000000000000 : ℝ), (8945298566829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022583069/10000000000 : ℝ)|^4327 ≤ (12323175443859/100000000000000 : ℝ)^3303
        have hw : |(-2022583069/10000000000 : ℝ)|=(2022583069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655747009/1250000000 : ℝ)|^4327 ≤ (8590066342903/20000000000000 : ℝ)^3303
        have hw : |(655747009/1250000000 : ℝ)|=(655747009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410780573/10000000000 : ℝ)|^4327 ≤ (8945298566829/20000000000000 : ℝ)^3303
        have hw : |(5410780573/10000000000 : ℝ)|=(5410780573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s7_5 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652832527/5000000000 : ℝ)*x 0 + (-485432027/2500000000 : ℝ)*x 1 + (2705390309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652832527/5000000000 : ℝ)^4327 ≤ (43591653536383/100000000000000 : ℝ)^3303 := by
    have hnat : (2652832527 : ℕ)^4327*100000000000000^3303 ≤ 43591653536383^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652832527 5000000000 43591653536383 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485432027/2500000000 : ℝ)^4327 ≤ (2920463280519/25000000000000 : ℝ)^3303 := by
    have hnat : (485432027 : ℕ)^4327*25000000000000^3303 ≤ 2920463280519^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485432027 2500000000 2920463280519 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705390309/5000000000 : ℝ)^4327 ≤ (11181623330361/25000000000000 : ℝ)^3303 := by
    have hnat : (2705390309 : ℕ)^4327*25000000000000^3303 ≤ 11181623330361^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705390309 5000000000 11181623330361 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652832527/5000000000 : ℝ), (-485432027/2500000000 : ℝ), (2705390309/5000000000 : ℝ)] ![(43591653536383/100000000000000 : ℝ), (2920463280519/25000000000000 : ℝ), (11181623330361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652832527/5000000000 : ℝ)|^4327 ≤ (43591653536383/100000000000000 : ℝ)^3303
        have hw : |(2652832527/5000000000 : ℝ)|=(2652832527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-485432027/2500000000 : ℝ)|^4327 ≤ (2920463280519/25000000000000 : ℝ)^3303
        have hw : |(-485432027/2500000000 : ℝ)|=(485432027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705390309/5000000000 : ℝ)|^4327 ≤ (11181623330361/25000000000000 : ℝ)^3303
        have hw : |(2705390309/5000000000 : ℝ)|=(2705390309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s7_6 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652832487/5000000000 : ℝ)*x 0 + (676347609/1250000000 : ℝ)*x 1 + (-485431967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652832487/5000000000 : ℝ)^4327 ≤ (21795826337663/50000000000000 : ℝ)^3303 := by
    have hnat : (2652832487 : ℕ)^4327*50000000000000^3303 ≤ 21795826337663^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652832487 5000000000 21795826337663 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676347609/1250000000 : ℝ)^4327 ≤ (22363248035989/50000000000000 : ℝ)^3303 := by
    have hnat : (676347609 : ℕ)^4327*50000000000000^3303 ≤ 22363248035989^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676347609 1250000000 22363248035989 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485431967/2500000000 : ℝ)^4327 ≤ (2920462807637/25000000000000 : ℝ)^3303 := by
    have hnat : (485431967 : ℕ)^4327*25000000000000^3303 ≤ 2920462807637^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485431967 2500000000 2920462807637 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652832487/5000000000 : ℝ), (676347609/1250000000 : ℝ), (-485431967/2500000000 : ℝ)] ![(21795826337663/50000000000000 : ℝ), (22363248035989/50000000000000 : ℝ), (2920462807637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652832487/5000000000 : ℝ)|^4327 ≤ (21795826337663/50000000000000 : ℝ)^3303
        have hw : |(2652832487/5000000000 : ℝ)|=(2652832487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676347609/1250000000 : ℝ)|^4327 ≤ (22363248035989/50000000000000 : ℝ)^3303
        have hw : |(676347609/1250000000 : ℝ)|=(676347609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485431967/2500000000 : ℝ)|^4327 ≤ (2920462807637/25000000000000 : ℝ)^3303
        have hw : |(-485431967/2500000000 : ℝ)|=(485431967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_s7_7 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160076069/5000000000 : ℝ)*x 0 + (449764717/1000000000 : ℝ)*x 1 + (4149201329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160076069/5000000000 : ℝ)^4327 ≤ (33303970952597/100000000000000 : ℝ)^3303 := by
    have hnat : (2160076069 : ℕ)^4327*100000000000000^3303 ≤ 33303970952597^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160076069 5000000000 33303970952597 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449764717/1000000000 : ℝ)^4327 ≤ (4388473806851/12500000000000 : ℝ)^3303 := by
    have hnat : (449764717 : ℕ)^4327*12500000000000^3303 ≤ 4388473806851^3303*1000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449764717 1000000000 4388473806851 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149201329/10000000000 : ℝ)^4327 ≤ (3948529822417/12500000000000 : ℝ)^3303 := by
    have hnat : (4149201329 : ℕ)^4327*12500000000000^3303 ≤ 3948529822417^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149201329 10000000000 3948529822417 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160076069/5000000000 : ℝ), (449764717/1000000000 : ℝ), (4149201329/10000000000 : ℝ)] ![(33303970952597/100000000000000 : ℝ), (4388473806851/12500000000000 : ℝ), (3948529822417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160076069/5000000000 : ℝ)|^4327 ≤ (33303970952597/100000000000000 : ℝ)^3303
        have hw : |(2160076069/5000000000 : ℝ)|=(2160076069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449764717/1000000000 : ℝ)|^4327 ≤ (4388473806851/12500000000000 : ℝ)^3303
        have hw : |(449764717/1000000000 : ℝ)|=(449764717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149201329/10000000000 : ℝ)|^4327 ≤ (3948529822417/12500000000000 : ℝ)^3303
        have hw : |(4149201329/10000000000 : ℝ)|=(4149201329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1367_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7361/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5603/50000 : ℝ) ^ (2163/512 : ℝ) ≤ (2411238551458739/25000000000000000000 : ℝ) := by
    have hpowers : (5603/50000 : ℝ)^2163 ≤ (2411238551458739/25000000000000000000 : ℝ)^512 := by
      have hnat : (5603 : ℕ)^2163*25000000000000000000^512 ≤ 2411238551458739^512*50000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5603 50000 2411238551458739 25000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5603/50000 : ℝ)) (X := (2411238551458739/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14723/100000 : ℝ) ^ (2163/512 : ℝ) ≤ (6111381788265163/20000000000000000000 : ℝ) := by
    have hpowers : (14723/100000 : ℝ)^2163 ≤ (6111381788265163/20000000000000000000 : ℝ)^512 := by
      have hnat : (14723 : ℕ)^2163*20000000000000000000^512 ≤ 6111381788265163^512*100000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14723 100000 6111381788265163 20000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14723/100000 : ℝ)) (X := (6111381788265163/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502411238551458739/12500000000000000000 : ℝ) ≤ (2500114143621067/2500000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (12502411238551458739/12500000000000000000 : ℝ)^512 ≤ (2500114143621067/2500000000000000 : ℝ)^2163 := by
      have hnat : (12502411238551458739 : ℕ)^512*2500000000000000^2163 ≤ 2500114143621067^2163*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502411238551458739 12500000000000000000 2500114143621067 2500000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500114143621067/2500000000000000 : ℝ)) (X := (12502411238551458739/12500000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040201863147160771/100000000000000000000 : ℝ) ≤ (10000951465399869/10000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (100040201863147160771/100000000000000000000 : ℝ)^512 ≤ (10000951465399869/10000000000000000 : ℝ)^2163 := by
      have hnat : (100040201863147160771 : ℕ)^512*10000000000000000^2163 ≤ 10000951465399869^2163*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040201863147160771 100000000000000000000 10000951465399869 10000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000951465399869/10000000000000000 : ℝ)) (X := (100040201863147160771/100000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006111381788265163/10000000000000000000 : ℝ) ≤ (1000144635631547/1000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (10006111381788265163/10000000000000000000 : ℝ)^512 ≤ (1000144635631547/1000000000000000 : ℝ)^2163 := by
      have hnat : (10006111381788265163 : ℕ)^512*1000000000000000^2163 ≤ 1000144635631547^2163*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006111381788265163 10000000000000000000 1000144635631547 1000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000144635631547/1000000000000000 : ℝ)) (X := (10006111381788265163/10000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2411238551458739/25000000000000000000 : ℝ) ≤ ((2197532142328795059/2198125000000000000 : ℝ)+2*(494890915601/351700000000000 : ℝ)*(5603/50000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (2197532142328795059/2198125000000000000 : ℝ)+2*(494890915601/351700000000000 : ℝ)*(5603/50000 : ℝ)=(2500114143621067/2500000000000000 : ℝ) by norm_num, show 1+2*(2411238551458739/25000000000000000000 : ℝ)=(12502411238551458739/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6111381788265163/20000000000000000000 : ℝ)+(2411238551458739/25000000000000000000 : ℝ) ≤ ((2197532142328795059/2198125000000000000 : ℝ)+(494890915601/351700000000000 : ℝ)*((14723/100000 : ℝ)+(5603/50000 : ℝ)))^(2163/512 : ℝ) := by
    rw [show (2197532142328795059/2198125000000000000 : ℝ)+(494890915601/351700000000000 : ℝ)*((14723/100000 : ℝ)+(5603/50000 : ℝ))=(10000951465399869/10000000000000000 : ℝ) by norm_num, show 1+(6111381788265163/20000000000000000000 : ℝ)+(2411238551458739/25000000000000000000 : ℝ)=(100040201863147160771/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6111381788265163/20000000000000000000 : ℝ) ≤ ((2197532142328795059/2198125000000000000 : ℝ)+2*(494890915601/351700000000000 : ℝ)*(14723/100000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (2197532142328795059/2198125000000000000 : ℝ)+2*(494890915601/351700000000000 : ℝ)*(14723/100000 : ℝ)=(1000144635631547/1000000000000000 : ℝ) by norm_num, show 1+2*(6111381788265163/20000000000000000000 : ℝ)=(10006111381788265163/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2197532142328795059/2198125000000000000 : ℝ)*(X 1 0+X 2 0)+(494890915601/351700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (2197532142328795059/2198125000000000000 : ℝ)) (alpha := (494890915601/351700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2197532142328795059/2198125000000000000 : ℝ)*(X 0 1+X 2 1)+(494890915601/351700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (2197532142328795059/2198125000000000000 : ℝ)) (alpha := (494890915601/351700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2197532142328795059/2198125000000000000 : ℝ)*(X 0 2+X 1 2)+(494890915601/351700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (2197532142328795059/2198125000000000000 : ℝ)) (alpha := (494890915601/351700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1011285691/5000000000 : ℝ)*X 0 0+(1082275833/2000000000 : ℝ)*X 0 1+(1311345097/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348542801/10000000000 : ℝ)*X 1 0+(-526782213/2500000000 : ℝ)*X 1 1+(5245380377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267427141/500000000 : ℝ)*X 2 0+(131134509/250000000 : ℝ)*X 2 1+(-2107128849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172805073/400000000 : ℝ)*X 0 0+(4147936199/10000000000 : ℝ)*X 0 1+(4498905949/10000000000 : ℝ)*X 0 2+(172805073/400000000 : ℝ)*X 1 0+(4147936199/10000000000 : ℝ)*X 1 1+(4498905949/10000000000 : ℝ)*X 1 2+(172805073/400000000 : ℝ)*X 2 0+(4147936199/10000000000 : ℝ)*X 2 1+(4498905949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2022583069/10000000000 : ℝ)*X 0 0+(655747009/1250000000 : ℝ)*X 0 1+(5410780573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652832527/5000000000 : ℝ)*X 1 0+(-485432027/2500000000 : ℝ)*X 1 1+(2705390309/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652832487/5000000000 : ℝ)*X 2 0+(676347609/1250000000 : ℝ)*X 2 1+(-485431967/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160076069/5000000000 : ℝ)*X 0 0+(449764717/1000000000 : ℝ)*X 0 1+(4149201329/10000000000 : ℝ)*X 0 2+(2160076069/5000000000 : ℝ)*X 1 0+(449764717/1000000000 : ℝ)*X 1 1+(4149201329/10000000000 : ℝ)*X 1 2+(2160076069/5000000000 : ℝ)*X 2 0+(449764717/1000000000 : ℝ)*X 2 1+(4149201329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243542163783370979749076763/27476562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (802292987/50000000000000 : ℝ)*(base19) + (751275429/50000000000000 : ℝ)*(base23) + (8252489/12500000000000 : ℝ)*(lower2) + (51583731/25000000000000 : ℝ)*(upper3) + (61509321/50000000000000 : ℝ)*(upper5) + (1109186210383203/25000000000000 : ℝ)*(major0) + (1109186210383203/25000000000000 : ℝ)*(major1) + (1109186210383203/25000000000000 : ℝ)*(major2) + (6024175258755049/100000000000000 : ℝ)*(sp0) + (301210345215789/5000000000000 : ℝ)*(sp1) + (376512937896931/6250000000000 : ℝ)*(sp2) + (712315918259543/25000000000000 : ℝ)*(sp3) + (6650029341/20000000000000 : ℝ)*(sp4) + (3441134251/20000000000000 : ℝ)*(sp7) + (1424640439354713/50000000000000 : ℝ)*(f.failure) + (3012104254450877/50000000000000 : ℝ)*(f.sum) + (32884767019283/17585000000000000000000000000 : ℝ)*base66 + (184435256681491463/13738281250000000000000000000000 : ℝ)*base67 + (387775310147700227/54953125000000000000000000000000 : ℝ)*base69 + (329891382771293977/54953125000000000000000000000000 : ℝ)*base71 + (6126937143259/8792500000000000000000000000 : ℝ)*base74 + (25174491712727287/13738281250000000000000000000000 : ℝ)*base76 + (425967747959106477/54953125000000000000000000000000 : ℝ)*base77 + (1604351493918856477/54953125000000000000000000000000 : ℝ)*base79 + (60218410808103/17585000000000000000000000000 : ℝ)*base82 + (13383819/1250000000000000000000 : ℝ)*base90 + (13383819/1250000000000000000000 : ℝ)*base92 + (13383819/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108482669778363807130383/17585000000000000000000000000 : ℝ) := by norm_num
    linear_combination (340116983/20000000000000 : ℝ)*(base19) + (10995631/500000000000 : ℝ)*(base23) + (679418019/100000000000000 : ℝ)*(lower1) + (64161279/50000000000000 : ℝ)*(upper3) + (13813877/6250000000000 : ℝ)*(lower4) + (2234404296542143/50000000000000 : ℝ)*(major0) + (2234404296542143/50000000000000 : ℝ)*(major1) + (2234404296542143/50000000000000 : ℝ)*(major2) + (21463115829/100000000000000 : ℝ)*(sp2) + (2408217151/100000000000000 : ℝ)*(sp3) + (3033872368214761/50000000000000 : ℝ)*(sp4) + (6067743035844607/100000000000000 : ℝ)*(sp5) + (6067721074187493/100000000000000 : ℝ)*(sp6) + (2869869835887033/100000000000000 : ℝ)*(sp7) + (358734030513023/12500000000000 : ℝ)*(f.failure) + (3033872368214761/50000000000000 : ℝ)*(f.sum) + (48977953421049/17585000000000000000000000000 : ℝ)*base66 + (227343504128903563/109906250000000000000000000000000 : ℝ)*base68 + (65558738251627687/109906250000000000000000000000000 : ℝ)*base69 + (1430440255981653563/109906250000000000000000000000000 : ℝ)*base72 + (25641655935369/17585000000000000000000000000 : ℝ)*base74 + (527807827709752687/109906250000000000000000000000000 : ℝ)*base75 + (3453924684579403563/109906250000000000000000000000000 : ℝ)*base78 + (346218225159096437/109906250000000000000000000000000 : ℝ)*base79 + (82681762798451/17585000000000000000000000000 : ℝ)*base81 + (2389651/312500000000000000000 : ℝ)*base89 + (2389651/312500000000000000000 : ℝ)*base91 + (2389651/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1367_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1367_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1367_box_0 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-928636247/5000000000 : ℝ)*x 0 + (5388892653/10000000000 : ℝ)*x 1 + (2694446279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928636247/5000000000 : ℝ)^4327 ≤ (2755190201963/25000000000000 : ℝ)^3303 := by
    have hnat : (928636247 : ℕ)^4327*25000000000000^3303 ≤ 2755190201963^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928636247 5000000000 2755190201963 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388892653/10000000000 : ℝ)^4327 ≤ (44489620101113/100000000000000 : ℝ)^3303 := by
    have hnat : (5388892653 : ℕ)^4327*100000000000000^3303 ≤ 44489620101113^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388892653 10000000000 44489620101113 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694446279/5000000000 : ℝ)^4327 ≤ (22244809536831/50000000000000 : ℝ)^3303 := by
    have hnat : (2694446279 : ℕ)^4327*50000000000000^3303 ≤ 22244809536831^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694446279 5000000000 22244809536831 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928636247/5000000000 : ℝ), (5388892653/10000000000 : ℝ), (2694446279/5000000000 : ℝ)] ![(2755190201963/25000000000000 : ℝ), (44489620101113/100000000000000 : ℝ), (22244809536831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928636247/5000000000 : ℝ)|^4327 ≤ (2755190201963/25000000000000 : ℝ)^3303
        have hw : |(-928636247/5000000000 : ℝ)|=(928636247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388892653/10000000000 : ℝ)|^4327 ≤ (44489620101113/100000000000000 : ℝ)^3303
        have hw : |(5388892653/10000000000 : ℝ)|=(5388892653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694446279/5000000000 : ℝ)|^4327 ≤ (22244809536831/50000000000000 : ℝ)^3303
        have hw : |(2694446279/5000000000 : ℝ)|=(2694446279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_1 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642741053/5000000000 : ℝ)*x 0 + (-399813839/2000000000 : ℝ)*x 1 + (5388892397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642741053/5000000000 : ℝ)^4327 ≤ (43374548425369/100000000000000 : ℝ)^3303 := by
    have hnat : (2642741053 : ℕ)^4327*100000000000000^3303 ≤ 43374548425369^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642741053 5000000000 43374548425369 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399813839/2000000000 : ℝ)^4327 ≤ (12135834235651/100000000000000 : ℝ)^3303 := by
    have hnat : (399813839 : ℕ)^4327*100000000000000^3303 ≤ 12135834235651^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399813839 2000000000 12135834235651 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388892397/10000000000 : ℝ)^4327 ≤ (44489617332403/100000000000000 : ℝ)^3303 := by
    have hnat : (5388892397 : ℕ)^4327*100000000000000^3303 ≤ 44489617332403^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388892397 10000000000 44489617332403 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642741053/5000000000 : ℝ), (-399813839/2000000000 : ℝ), (5388892397/10000000000 : ℝ)] ![(43374548425369/100000000000000 : ℝ), (12135834235651/100000000000000 : ℝ), (44489617332403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642741053/5000000000 : ℝ)|^4327 ≤ (43374548425369/100000000000000 : ℝ)^3303
        have hw : |(2642741053/5000000000 : ℝ)|=(2642741053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399813839/2000000000 : ℝ)|^4327 ≤ (12135834235651/100000000000000 : ℝ)^3303
        have hw : |(-399813839/2000000000 : ℝ)|=(399813839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388892397/10000000000 : ℝ)|^4327 ≤ (44489617332403/100000000000000 : ℝ)^3303
        have hw : |(5388892397/10000000000 : ℝ)|=(5388892397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_2 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285481647/10000000000 : ℝ)*x 0 + (1347223231/2500000000 : ℝ)*x 1 + (-999534549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285481647/10000000000 : ℝ)^4327 ≤ (4337454349089/10000000000000 : ℝ)^3303 := by
    have hnat : (5285481647 : ℕ)^4327*10000000000000^3303 ≤ 4337454349089^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285481647 10000000000 4337454349089 10000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347223231/2500000000 : ℝ)^4327 ≤ (11122405758013/25000000000000 : ℝ)^3303 := by
    have hnat : (1347223231 : ℕ)^4327*25000000000000^3303 ≤ 11122405758013^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347223231 2500000000 11122405758013 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999534549/5000000000 : ℝ)^4327 ≤ (12135833464229/100000000000000 : ℝ)^3303 := by
    have hnat : (999534549 : ℕ)^4327*100000000000000^3303 ≤ 12135833464229^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999534549 5000000000 12135833464229 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285481647/10000000000 : ℝ), (1347223231/2500000000 : ℝ), (-999534549/5000000000 : ℝ)] ![(4337454349089/10000000000000 : ℝ), (11122405758013/25000000000000 : ℝ), (12135833464229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285481647/10000000000 : ℝ)|^4327 ≤ (4337454349089/10000000000000 : ℝ)^3303
        have hw : |(5285481647/10000000000 : ℝ)|=(5285481647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347223231/2500000000 : ℝ)|^4327 ≤ (11122405758013/25000000000000 : ℝ)^3303
        have hw : |(1347223231/2500000000 : ℝ)|=(1347223231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-999534549/5000000000 : ℝ)|^4327 ≤ (12135833464229/100000000000000 : ℝ)^3303
        have hw : |(-999534549/5000000000 : ℝ)|=(999534549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_3 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (223387209/500000000 : ℝ)*x 0 + (4250152957/10000000000 : ℝ)*x 1 + (2125076603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223387209/500000000 : ℝ)^4327 ≤ (8700581171481/25000000000000 : ℝ)^3303 := by
    have hnat : (223387209 : ℕ)^4327*25000000000000^3303 ≤ 8700581171481^3303*500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223387209 500000000 8700581171481 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250152957/10000000000 : ℝ)^4327 ≤ (52158138239/160000000000 : ℝ)^3303 := by
    have hnat : (4250152957 : ℕ)^4327*160000000000^3303 ≤ 52158138239^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250152957 10000000000 52158138239 160000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125076603/5000000000 : ℝ)^4327 ≤ (6519767780261/20000000000000 : ℝ)^3303 := by
    have hnat : (2125076603 : ℕ)^4327*20000000000000^3303 ≤ 6519767780261^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125076603 5000000000 6519767780261 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223387209/500000000 : ℝ), (4250152957/10000000000 : ℝ), (2125076603/5000000000 : ℝ)] ![(8700581171481/25000000000000 : ℝ), (52158138239/160000000000 : ℝ), (6519767780261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223387209/500000000 : ℝ)|^4327 ≤ (8700581171481/25000000000000 : ℝ)^3303
        have hw : |(223387209/500000000 : ℝ)|=(223387209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250152957/10000000000 : ℝ)|^4327 ≤ (52158138239/160000000000 : ℝ)^3303
        have hw : |(4250152957/10000000000 : ℝ)|=(4250152957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125076603/5000000000 : ℝ)|^4327 ≤ (6519767780261/20000000000000 : ℝ)^3303
        have hw : |(2125076603/5000000000 : ℝ)|=(2125076603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_4 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190617019/10000000000 : ℝ)*x 0 + (2632725973/5000000000 : ℝ)*x 1 + (1053090311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190617019/10000000000 : ℝ)^4327 ≤ (6840661306459/50000000000000 : ℝ)^3303 := by
    have hnat : (2190617019 : ℕ)^4327*50000000000000^3303 ≤ 6840661306459^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190617019 10000000000 6840661306459 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632725973/5000000000 : ℝ)^4327 ≤ (10789835196831/25000000000000 : ℝ)^3303 := by
    have hnat : (2632725973 : ℕ)^4327*25000000000000^3303 ≤ 10789835196831^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632725973 5000000000 10789835196831 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053090311/2000000000 : ℝ)^4327 ≤ (5394917073603/12500000000000 : ℝ)^3303 := by
    have hnat : (1053090311 : ℕ)^4327*12500000000000^3303 ≤ 5394917073603^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053090311 2000000000 5394917073603 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190617019/10000000000 : ℝ), (2632725973/5000000000 : ℝ), (1053090311/2000000000 : ℝ)] ![(6840661306459/50000000000000 : ℝ), (10789835196831/25000000000000 : ℝ), (5394917073603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190617019/10000000000 : ℝ)|^4327 ≤ (6840661306459/50000000000000 : ℝ)^3303
        have hw : |(-2190617019/10000000000 : ℝ)|=(2190617019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632725973/5000000000 : ℝ)|^4327 ≤ (10789835196831/25000000000000 : ℝ)^3303
        have hw : |(2632725973/5000000000 : ℝ)|=(2632725973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053090311/2000000000 : ℝ)|^4327 ≤ (5394917073603/12500000000000 : ℝ)^3303
        have hw : |(1053090311/2000000000 : ℝ)|=(1053090311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_5 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671511689/1250000000 : ℝ)*x 0 + (-2048774297/10000000000 : ℝ)*x 1 + (5265451441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671511689/1250000000 : ℝ)^4327 ≤ (2215401033193/5000000000000 : ℝ)^3303 := by
    have hnat : (671511689 : ℕ)^4327*5000000000000^3303 ≤ 2215401033193^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671511689 1250000000 2215401033193 5000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2048774297/10000000000 : ℝ)^4327 ≤ (2506528791639/20000000000000 : ℝ)^3303 := by
    have hnat : (2048774297 : ℕ)^4327*20000000000000^3303 ≤ 2506528791639^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048774297 10000000000 2506528791639 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265451441/10000000000 : ℝ)^4327 ≤ (43159335364709/100000000000000 : ℝ)^3303 := by
    have hnat : (5265451441 : ℕ)^4327*100000000000000^3303 ≤ 43159335364709^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265451441 10000000000 43159335364709 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671511689/1250000000 : ℝ), (-2048774297/10000000000 : ℝ), (5265451441/10000000000 : ℝ)] ![(2215401033193/5000000000000 : ℝ), (2506528791639/20000000000000 : ℝ), (43159335364709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671511689/1250000000 : ℝ)|^4327 ≤ (2215401033193/5000000000000 : ℝ)^3303
        have hw : |(671511689/1250000000 : ℝ)|=(671511689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2048774297/10000000000 : ℝ)|^4327 ≤ (2506528791639/20000000000000 : ℝ)^3303
        have hw : |(-2048774297/10000000000 : ℝ)|=(2048774297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265451441/10000000000 : ℝ)|^4327 ≤ (43159335364709/100000000000000 : ℝ)^3303
        have hw : |(5265451441/10000000000 : ℝ)|=(5265451441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_6 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686046811/5000000000 : ℝ)*x 0 + (2632725863/5000000000 : ℝ)*x 1 + (-2048773767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686046811/5000000000 : ℝ)^4327 ≤ (44308021852389/100000000000000 : ℝ)^3303 := by
    have hnat : (2686046811 : ℕ)^4327*100000000000000^3303 ≤ 44308021852389^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686046811 5000000000 44308021852389 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632725863/5000000000 : ℝ)^4327 ≤ (43159338424997/100000000000000 : ℝ)^3303 := by
    have hnat : (2632725863 : ℕ)^4327*100000000000000^3303 ≤ 43159338424997^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632725863 5000000000 43159338424997 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048773767/10000000000 : ℝ)^4327 ≤ (2506527942199/20000000000000 : ℝ)^3303 := by
    have hnat : (2048773767 : ℕ)^4327*20000000000000^3303 ≤ 2506527942199^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048773767 10000000000 2506527942199 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686046811/5000000000 : ℝ), (2632725863/5000000000 : ℝ), (-2048773767/10000000000 : ℝ)] ![(44308021852389/100000000000000 : ℝ), (43159338424997/100000000000000 : ℝ), (2506527942199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686046811/5000000000 : ℝ)|^4327 ≤ (44308021852389/100000000000000 : ℝ)^3303
        have hw : |(2686046811/5000000000 : ℝ)|=(2686046811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632725863/5000000000 : ℝ)|^4327 ≤ (43159338424997/100000000000000 : ℝ)^3303
        have hw : |(2632725863/5000000000 : ℝ)|=(2632725863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048773767/10000000000 : ℝ)|^4327 ≤ (2506527942199/20000000000000 : ℝ)^3303
        have hw : |(-2048773767/10000000000 : ℝ)|=(2048773767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_7 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042886909/2500000000 : ℝ)*x 0 + (219909923/500000000 : ℝ)*x 1 + (4398198697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042886909/2500000000 : ℝ)^4327 ≤ (15905645502509/50000000000000 : ℝ)^3303 := by
    have hnat : (1042886909 : ℕ)^4327*50000000000000^3303 ≤ 15905645502509^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042886909 2500000000 15905645502509 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219909923/500000000 : ℝ)^4327 ≤ (4261794160571/12500000000000 : ℝ)^3303 := by
    have hnat : (219909923 : ℕ)^4327*12500000000000^3303 ≤ 4261794160571^3303*500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219909923 500000000 4261794160571 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4398198697/10000000000 : ℝ)^4327 ≤ (4261794461417/12500000000000 : ℝ)^3303 := by
    have hnat : (4398198697 : ℕ)^4327*12500000000000^3303 ≤ 4261794461417^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4398198697 10000000000 4261794461417 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042886909/2500000000 : ℝ), (219909923/500000000 : ℝ), (4398198697/10000000000 : ℝ)] ![(15905645502509/50000000000000 : ℝ), (4261794160571/12500000000000 : ℝ), (4261794461417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042886909/2500000000 : ℝ)|^4327 ≤ (15905645502509/50000000000000 : ℝ)^3303
        have hw : |(1042886909/2500000000 : ℝ)|=(1042886909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219909923/500000000 : ℝ)|^4327 ≤ (4261794160571/12500000000000 : ℝ)^3303
        have hw : |(219909923/500000000 : ℝ)|=(219909923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4398198697/10000000000 : ℝ)|^4327 ≤ (4261794461417/12500000000000 : ℝ)^3303
        have hw : |(4398198697/10000000000 : ℝ)|=(4398198697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_8 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-26506891/125000000 : ℝ)*x 0 + (2590177413/5000000000 : ℝ)*x 1 + (5402901261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26506891/125000000 : ℝ)^4327 ≤ (3277733463091/25000000000000 : ℝ)^3303 := by
    have hnat : (26506891 : ℕ)^4327*25000000000000^3303 ≤ 3277733463091^3303*125000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26506891 125000000 3277733463091 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590177413/5000000000 : ℝ)^4327 ≤ (264049238113/625000000000 : ℝ)^3303 := by
    have hnat : (2590177413 : ℕ)^4327*625000000000^3303 ≤ 264049238113^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590177413 5000000000 264049238113 625000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402901261/10000000000 : ℝ)^4327 ≤ (22320594017497/50000000000000 : ℝ)^3303 := by
    have hnat : (5402901261 : ℕ)^4327*50000000000000^3303 ≤ 22320594017497^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402901261 10000000000 22320594017497 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26506891/125000000 : ℝ), (2590177413/5000000000 : ℝ), (5402901261/10000000000 : ℝ)] ![(3277733463091/25000000000000 : ℝ), (264049238113/625000000000 : ℝ), (22320594017497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26506891/125000000 : ℝ)|^4327 ≤ (3277733463091/25000000000000 : ℝ)^3303
        have hw : |(-26506891/125000000 : ℝ)|=(26506891/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590177413/5000000000 : ℝ)|^4327 ≤ (264049238113/625000000000 : ℝ)^3303
        have hw : |(2590177413/5000000000 : ℝ)|=(2590177413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402901261/10000000000 : ℝ)|^4327 ≤ (22320594017497/50000000000000 : ℝ)^3303
        have hw : |(5402901261/10000000000 : ℝ)|=(5402901261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_9 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82431999/156250000 : ℝ)*x 0 + (-199329767/1000000000 : ℝ)*x 1 + (2701450643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82431999/156250000 : ℝ)^4327 ≤ (21634428340617/50000000000000 : ℝ)^3303 := by
    have hnat : (82431999 : ℕ)^4327*50000000000000^3303 ≤ 21634428340617^3303*156250000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82431999 156250000 21634428340617 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199329767/1000000000 : ℝ)^4327 ≤ (302248874989/2500000000000 : ℝ)^3303 := by
    have hnat : (199329767 : ℕ)^4327*2500000000000^3303 ≤ 302248874989^3303*1000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199329767 1000000000 302248874989 2500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701450643/5000000000 : ℝ)^4327 ≤ (44641188305593/100000000000000 : ℝ)^3303 := by
    have hnat : (2701450643 : ℕ)^4327*100000000000000^3303 ≤ 44641188305593^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701450643 5000000000 44641188305593 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82431999/156250000 : ℝ), (-199329767/1000000000 : ℝ), (2701450643/5000000000 : ℝ)] ![(21634428340617/50000000000000 : ℝ), (302248874989/2500000000000 : ℝ), (44641188305593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82431999/156250000 : ℝ)|^4327 ≤ (21634428340617/50000000000000 : ℝ)^3303
        have hw : |(82431999/156250000 : ℝ)|=(82431999/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199329767/1000000000 : ℝ)|^4327 ≤ (302248874989/2500000000000 : ℝ)^3303
        have hw : |(-199329767/1000000000 : ℝ)|=(199329767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701450643/5000000000 : ℝ)|^4327 ≤ (44641188305593/100000000000000 : ℝ)^3303
        have hw : |(2701450643/5000000000 : ℝ)|=(2701450643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_10 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329727987/625000000 : ℝ)*x 0 + (5402901307/10000000000 : ℝ)*x 1 + (-398659567/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329727987/625000000 : ℝ)^4327 ≤ (5408606891757/12500000000000 : ℝ)^3303 := by
    have hnat : (329727987 : ℕ)^4327*12500000000000^3303 ≤ 5408606891757^3303*625000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329727987 625000000 5408606891757 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402901307/10000000000 : ℝ)^4327 ≤ (44641188532897/100000000000000 : ℝ)^3303 := by
    have hnat : (5402901307 : ℕ)^4327*100000000000000^3303 ≤ 44641188532897^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402901307 10000000000 44641188532897 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398659567/2000000000 : ℝ)^4327 ≤ (3022489077649/25000000000000 : ℝ)^3303 := by
    have hnat : (398659567 : ℕ)^4327*25000000000000^3303 ≤ 3022489077649^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398659567 2000000000 3022489077649 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329727987/625000000 : ℝ), (5402901307/10000000000 : ℝ), (-398659567/2000000000 : ℝ)] ![(5408606891757/12500000000000 : ℝ), (44641188532897/100000000000000 : ℝ), (3022489077649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329727987/625000000 : ℝ)|^4327 ≤ (5408606891757/12500000000000 : ℝ)^3303
        have hw : |(329727987/625000000 : ℝ)|=(329727987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402901307/10000000000 : ℝ)|^4327 ≤ (44641188532897/100000000000000 : ℝ)^3303
        have hw : |(5402901307/10000000000 : ℝ)|=(5402901307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398659567/2000000000 : ℝ)|^4327 ≤ (3022489077649/25000000000000 : ℝ)^3303
        have hw : |(-398659567/2000000000 : ℝ)|=(398659567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_11 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (140649989/312500000 : ℝ)*x 0 + (4233337973/10000000000 : ℝ)*x 1 + (2116668999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140649989/312500000 : ℝ)^4327 ≤ (35140030502549/100000000000000 : ℝ)^3303 := by
    have hnat : (140649989 : ℕ)^4327*100000000000000^3303 ≤ 35140030502549^3303*312500000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140649989 312500000 35140030502549 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233337973/10000000000 : ℝ)^4327 ≤ (16214992307791/50000000000000 : ℝ)^3303 := by
    have hnat : (4233337973 : ℕ)^4327*50000000000000^3303 ≤ 16214992307791^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233337973 10000000000 16214992307791 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116668999/5000000000 : ℝ)^4327 ≤ (32429984866471/100000000000000 : ℝ)^3303 := by
    have hnat : (2116668999 : ℕ)^4327*100000000000000^3303 ≤ 32429984866471^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116668999 5000000000 32429984866471 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140649989/312500000 : ℝ), (4233337973/10000000000 : ℝ), (2116668999/5000000000 : ℝ)] ![(35140030502549/100000000000000 : ℝ), (16214992307791/50000000000000 : ℝ), (32429984866471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140649989/312500000 : ℝ)|^4327 ≤ (35140030502549/100000000000000 : ℝ)^3303
        have hw : |(140649989/312500000 : ℝ)|=(140649989/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233337973/10000000000 : ℝ)|^4327 ≤ (16214992307791/50000000000000 : ℝ)^3303
        have hw : |(4233337973/10000000000 : ℝ)|=(4233337973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116668999/5000000000 : ℝ)|^4327 ≤ (32429984866471/100000000000000 : ℝ)^3303
        have hw : |(2116668999/5000000000 : ℝ)|=(2116668999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_12 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-385525639/2000000000 : ℝ)*x 0 + (1367959759/2500000000 : ℝ)*x 1 + (5254362929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385525639/2000000000 : ℝ)^4327 ≤ (11570851804083/100000000000000 : ℝ)^3303 := by
    have hnat : (385525639 : ℕ)^4327*100000000000000^3303 ≤ 11570851804083^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385525639 2000000000 11570851804083 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367959759/2500000000 : ℝ)^4327 ≤ (22694420372831/50000000000000 : ℝ)^3303 := by
    have hnat : (1367959759 : ℕ)^4327*50000000000000^3303 ≤ 22694420372831^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367959759 2500000000 22694420372831 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254362929/10000000000 : ℝ)^4327 ≤ (5380038429819/12500000000000 : ℝ)^3303 := by
    have hnat : (5254362929 : ℕ)^4327*12500000000000^3303 ≤ 5380038429819^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254362929 10000000000 5380038429819 12500000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385525639/2000000000 : ℝ), (1367959759/2500000000 : ℝ), (5254362929/10000000000 : ℝ)] ![(11570851804083/100000000000000 : ℝ), (22694420372831/50000000000000 : ℝ), (5380038429819/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385525639/2000000000 : ℝ)|^4327 ≤ (11570851804083/100000000000000 : ℝ)^3303
        have hw : |(-385525639/2000000000 : ℝ)|=(385525639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367959759/2500000000 : ℝ)|^4327 ≤ (22694420372831/50000000000000 : ℝ)^3303
        have hw : |(1367959759/2500000000 : ℝ)|=(1367959759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254362929/10000000000 : ℝ)|^4327 ≤ (5380038429819/12500000000000 : ℝ)^3303
        have hw : |(5254362929/10000000000 : ℝ)|=(5254362929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_13 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537987117/1000000000 : ℝ)*x 0 + (-1026568529/5000000000 : ℝ)*x 1 + (656795367/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537987117/1000000000 : ℝ)^4327 ≤ (44392075628889/100000000000000 : ℝ)^3303 := by
    have hnat : (537987117 : ℕ)^4327*100000000000000^3303 ≤ 44392075628889^3303*1000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537987117 1000000000 44392075628889 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026568529/5000000000 : ℝ)^4327 ≤ (12567616853667/100000000000000 : ℝ)^3303 := by
    have hnat : (1026568529 : ℕ)^4327*100000000000000^3303 ≤ 12567616853667^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026568529 5000000000 12567616853667 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656795367/1250000000 : ℝ)^4327 ≤ (10760076878417/25000000000000 : ℝ)^3303 := by
    have hnat : (656795367 : ℕ)^4327*25000000000000^3303 ≤ 10760076878417^3303*1250000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656795367 1250000000 10760076878417 25000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537987117/1000000000 : ℝ), (-1026568529/5000000000 : ℝ), (656795367/1250000000 : ℝ)] ![(44392075628889/100000000000000 : ℝ), (12567616853667/100000000000000 : ℝ), (10760076878417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537987117/1000000000 : ℝ)|^4327 ≤ (44392075628889/100000000000000 : ℝ)^3303
        have hw : |(537987117/1000000000 : ℝ)|=(537987117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026568529/5000000000 : ℝ)|^4327 ≤ (12567616853667/100000000000000 : ℝ)^3303
        have hw : |(-1026568529/5000000000 : ℝ)|=(1026568529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656795367/1250000000 : ℝ)|^4327 ≤ (10760076878417/25000000000000 : ℝ)^3303
        have hw : |(656795367/1250000000 : ℝ)|=(656795367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_14 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379871469/10000000000 : ℝ)*x 0 + (5254362673/10000000000 : ℝ)*x 1 + (-1026568503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379871469/10000000000 : ℝ)^4327 ≤ (2774504928811/6250000000000 : ℝ)^3303 := by
    have hnat : (5379871469 : ℕ)^4327*6250000000000^3303 ≤ 2774504928811^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379871469 10000000000 2774504928811 6250000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254362673/10000000000 : ℝ)^4327 ≤ (43040304691457/100000000000000 : ℝ)^3303 := by
    have hnat : (5254362673 : ℕ)^4327*100000000000000^3303 ≤ 43040304691457^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254362673 10000000000 43040304691457 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026568503/5000000000 : ℝ)^4327 ≤ (6283808218343/50000000000000 : ℝ)^3303 := by
    have hnat : (1026568503 : ℕ)^4327*50000000000000^3303 ≤ 6283808218343^3303*5000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026568503 5000000000 6283808218343 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379871469/10000000000 : ℝ), (5254362673/10000000000 : ℝ), (-1026568503/5000000000 : ℝ)] ![(2774504928811/6250000000000 : ℝ), (43040304691457/100000000000000 : ℝ), (6283808218343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379871469/10000000000 : ℝ)|^4327 ≤ (2774504928811/6250000000000 : ℝ)^3303
        have hw : |(5379871469/10000000000 : ℝ)|=(5379871469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254362673/10000000000 : ℝ)|^4327 ≤ (43040304691457/100000000000000 : ℝ)^3303
        have hw : |(5254362673/10000000000 : ℝ)|=(5254362673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026568503/5000000000 : ℝ)|^4327 ≤ (6283808218343/50000000000000 : ℝ)^3303
        have hw : |(-1026568503/5000000000 : ℝ)|=(1026568503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1367_box_15 (p : ℝ) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4144490999/10000000000 : ℝ)*x 0 + (882297441/2000000000 : ℝ)*x 1 + (1102871793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4144490999/10000000000 : ℝ)^4327 ≤ (6308253855477/20000000000000 : ℝ)^3303 := by
    have hnat : (4144490999 : ℕ)^4327*20000000000000^3303 ≤ 6308253855477^3303*10000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144490999 10000000000 6308253855477 20000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882297441/2000000000 : ℝ)^4327 ≤ (34229365522847/100000000000000 : ℝ)^3303 := by
    have hnat : (882297441 : ℕ)^4327*100000000000000^3303 ≤ 34229365522847^3303*2000000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882297441 2000000000 34229365522847 100000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102871793/2500000000 : ℝ)^4327 ≤ (17114682593707/50000000000000 : ℝ)^3303 := by
    have hnat : (1102871793 : ℕ)^4327*50000000000000^3303 ≤ 17114682593707^3303*2500000000^4327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102871793 2500000000 17114682593707 50000000000000 4327 3303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4327/1024 : ℝ)) 4327 3303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4144490999/10000000000 : ℝ), (882297441/2000000000 : ℝ), (1102871793/2500000000 : ℝ)] ![(6308253855477/20000000000000 : ℝ), (34229365522847/100000000000000 : ℝ), (17114682593707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4144490999/10000000000 : ℝ)|^4327 ≤ (6308253855477/20000000000000 : ℝ)^3303
        have hw : |(4144490999/10000000000 : ℝ)|=(4144490999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882297441/2000000000 : ℝ)|^4327 ≤ (34229365522847/100000000000000 : ℝ)^3303
        have hw : |(882297441/2000000000 : ℝ)|=(882297441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102871793/2500000000 : ℝ)|^4327 ≤ (17114682593707/50000000000000 : ℝ)^3303
        have hw : |(1102871793/2500000000 : ℝ)|=(1102871793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1367_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31433/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5899/10000 : ℝ) ∧ (80099/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84449/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11207/100000 : ℝ) ^ (2163/512 : ℝ) ≤ (4824295415734379/50000000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^2163 ≤ (4824295415734379/50000000000000000000 : ℝ)^512 := by
      have hnat : (11207 : ℕ)^2163*50000000000000000000^512 ≤ 4824295415734379^512*100000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 4824295415734379 50000000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (4824295415734379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7361/50000 : ℝ) ^ (2163/512 : ℝ) ≤ (190925886994457/625000000000000000 : ℝ) := by
    have hpowers : (7361/50000 : ℝ)^2163 ≤ (190925886994457/625000000000000000 : ℝ)^512 := by
      have hnat : (7361 : ℕ)^2163*625000000000000000^512 ≤ 190925886994457^512*50000^2163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7361 50000 190925886994457 625000000000000000 2163 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7361/50000 : ℝ)) (X := (190925886994457/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004824295415734379/25000000000000000000 : ℝ) ≤ (2000091349324559/2000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (25004824295415734379/25000000000000000000 : ℝ)^512 ≤ (2000091349324559/2000000000000000 : ℝ)^2163 := by
      have hnat : (25004824295415734379 : ℕ)^512*2000000000000000^2163 ≤ 2000091349324559^2163*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004824295415734379 25000000000000000000 2000091349324559 2000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000091349324559/2000000000000000 : ℝ)) (X := (25004824295415734379/25000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020098366375290939/50000000000000000000 : ℝ) ≤ (5000475671998193/5000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (50020098366375290939/50000000000000000000 : ℝ)^512 ≤ (5000475671998193/5000000000000000 : ℝ)^2163 := by
      have hnat : (50020098366375290939 : ℕ)^512*5000000000000000^2163 ≤ 5000475671998193^2163*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020098366375290939 50000000000000000000 5000475671998193 5000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000475671998193/5000000000000000 : ℝ)) (X := (50020098366375290939/50000000000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (312690925886994457/312500000000000000 : ℝ) ≤ (10001445941369977/10000000000000000 : ℝ) ^ (2163/512 : ℝ) := by
    have hpowers : (312690925886994457/312500000000000000 : ℝ)^512 ≤ (10001445941369977/10000000000000000 : ℝ)^2163 := by
      have hnat : (312690925886994457 : ℕ)^512*10000000000000000^2163 ≤ 10001445941369977^2163*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312690925886994457 312500000000000000 10001445941369977 10000000000000000 512 2163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001445941369977/10000000000000000 : ℝ)) (X := (312690925886994457/312500000000000000 : ℝ)) (by norm_num) 2163 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4824295415734379/50000000000000000000 : ℝ) ≤ ((35140519558847455751/35150000000000000000 : ℝ)+2*(494597373591/351500000000000 : ℝ)*(11207/100000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (35140519558847455751/35150000000000000000 : ℝ)+2*(494597373591/351500000000000 : ℝ)*(11207/100000 : ℝ)=(2000091349324559/2000000000000000 : ℝ) by norm_num, show 1+2*(4824295415734379/50000000000000000000 : ℝ)=(25004824295415734379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(190925886994457/625000000000000000 : ℝ)+(4824295415734379/50000000000000000000 : ℝ) ≤ ((35140519558847455751/35150000000000000000 : ℝ)+(494597373591/351500000000000 : ℝ)*((7361/50000 : ℝ)+(11207/100000 : ℝ)))^(2163/512 : ℝ) := by
    rw [show (35140519558847455751/35150000000000000000 : ℝ)+(494597373591/351500000000000 : ℝ)*((7361/50000 : ℝ)+(11207/100000 : ℝ))=(5000475671998193/5000000000000000 : ℝ) by norm_num, show 1+(190925886994457/625000000000000000 : ℝ)+(4824295415734379/50000000000000000000 : ℝ)=(50020098366375290939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(190925886994457/625000000000000000 : ℝ) ≤ ((35140519558847455751/35150000000000000000 : ℝ)+2*(494597373591/351500000000000 : ℝ)*(7361/50000 : ℝ))^(2163/512 : ℝ) := by
    rw [show (35140519558847455751/35150000000000000000 : ℝ)+2*(494597373591/351500000000000 : ℝ)*(7361/50000 : ℝ)=(10001445941369977/10000000000000000 : ℝ) by norm_num, show 1+2*(190925886994457/625000000000000000 : ℝ)=(312690925886994457/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35140519558847455751/35150000000000000000 : ℝ)*(X 1 0+X 2 0)+(494597373591/351500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (35140519558847455751/35150000000000000000 : ℝ)) (alpha := (494597373591/351500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35140519558847455751/35150000000000000000 : ℝ)*(X 0 1+X 2 1)+(494597373591/351500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (35140519558847455751/35150000000000000000 : ℝ)) (alpha := (494597373591/351500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35140519558847455751/35150000000000000000 : ℝ)*(X 0 2+X 1 2)+(494597373591/351500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2163/512 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (35140519558847455751/35150000000000000000 : ℝ)) (alpha := (494597373591/351500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-928636247/5000000000 : ℝ)*X 0 0+(5388892653/10000000000 : ℝ)*X 0 1+(2694446279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642741053/5000000000 : ℝ)*X 1 0+(-399813839/2000000000 : ℝ)*X 1 1+(5388892397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285481647/10000000000 : ℝ)*X 2 0+(1347223231/2500000000 : ℝ)*X 2 1+(-999534549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((223387209/500000000 : ℝ)*X 0 0+(4250152957/10000000000 : ℝ)*X 0 1+(2125076603/5000000000 : ℝ)*X 0 2+(223387209/500000000 : ℝ)*X 1 0+(4250152957/10000000000 : ℝ)*X 1 1+(2125076603/5000000000 : ℝ)*X 1 2+(223387209/500000000 : ℝ)*X 2 0+(4250152957/10000000000 : ℝ)*X 2 1+(2125076603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2190617019/10000000000 : ℝ)*X 0 0+(2632725973/5000000000 : ℝ)*X 0 1+(1053090311/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((671511689/1250000000 : ℝ)*X 1 0+(-2048774297/10000000000 : ℝ)*X 1 1+(5265451441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686046811/5000000000 : ℝ)*X 2 0+(2632725863/5000000000 : ℝ)*X 2 1+(-2048773767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042886909/2500000000 : ℝ)*X 0 0+(219909923/500000000 : ℝ)*X 0 1+(4398198697/10000000000 : ℝ)*X 0 2+(1042886909/2500000000 : ℝ)*X 1 0+(219909923/500000000 : ℝ)*X 1 1+(4398198697/10000000000 : ℝ)*X 1 2+(1042886909/2500000000 : ℝ)*X 2 0+(219909923/500000000 : ℝ)*X 2 1+(4398198697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-26506891/125000000 : ℝ)*X 0 0+(2590177413/5000000000 : ℝ)*X 0 1+(5402901261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((82431999/156250000 : ℝ)*X 1 0+(-199329767/1000000000 : ℝ)*X 1 1+(2701450643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((329727987/625000000 : ℝ)*X 2 0+(5402901307/10000000000 : ℝ)*X 2 1+(-398659567/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((140649989/312500000 : ℝ)*X 0 0+(4233337973/10000000000 : ℝ)*X 0 1+(2116668999/5000000000 : ℝ)*X 0 2+(140649989/312500000 : ℝ)*X 1 0+(4233337973/10000000000 : ℝ)*X 1 1+(2116668999/5000000000 : ℝ)*X 1 2+(140649989/312500000 : ℝ)*X 2 0+(4233337973/10000000000 : ℝ)*X 2 1+(2116668999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-385525639/2000000000 : ℝ)*X 0 0+(1367959759/2500000000 : ℝ)*X 0 1+(5254362929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((537987117/1000000000 : ℝ)*X 1 0+(-1026568529/5000000000 : ℝ)*X 1 1+(656795367/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379871469/10000000000 : ℝ)*X 2 0+(5254362673/10000000000 : ℝ)*X 2 1+(-1026568503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4144490999/10000000000 : ℝ)*X 0 0+(882297441/2000000000 : ℝ)*X 0 1+(1102871793/2500000000 : ℝ)*X 0 2+(4144490999/10000000000 : ℝ)*X 1 0+(882297441/2000000000 : ℝ)*X 1 1+(1102871793/2500000000 : ℝ)*X 1 2+(4144490999/10000000000 : ℝ)*X 2 0+(882297441/2000000000 : ℝ)*X 2 1+(1102871793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1367_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31433/50000 : ℝ) ≤ (-17262910325466096074568031852107/27460937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (965787/20000000000000 : ℝ)*(upper0) + (125651377/100000000000000 : ℝ)*(lower1) + (101834613/50000000000000 : ℝ)*(lower2) + (9052687/25000000000000 : ℝ)*(lower3) + (46069948238123/1562500000000 : ℝ)*(major0) + (46069948238123/1562500000000 : ℝ)*(major1) + (46069948238123/1562500000000 : ℝ)*(major2) + (19746730433/100000000000000 : ℝ)*(sp1) + (1342575911/100000000000000 : ℝ)*(sp2) + (100609651020953/2500000000000 : ℝ)*(sp4) + (2012187091653317/50000000000000 : ℝ)*(sp5) + (1006098146865289/25000000000000 : ℝ)*(sp6) + (236689243644071/12500000000000 : ℝ)*(sp7) + (7889198947/100000000000000 : ℝ)*(sp8) + (236689243644071/12500000000000 : ℝ)*(f.failure) + (4024393930037067/100000000000000 : ℝ)*(f.sum) + (5797350478781/2196875000000000000000000000 : ℝ)*base66 + (535494084899189123/54921875000000000000000000000000 : ℝ)*base67 + (82175812159049031/6865234375000000000000000000000 : ℝ)*base69 + (554676937508876623/54921875000000000000000000000000 : ℝ)*base71 + (572572541881827/17575000000000000000000000000 : ℝ)*base73 + (11365118502454203/3432617187500000000000000000000 : ℝ)*base75 + (63965283366586749/27460937500000000000000000000000 : ℝ)*base77 + (1977283415177782873/54921875000000000000000000000000 : ℝ)*base79 + (24474453646451/8787500000000000000000000000 : ℝ)*base81 + (2838773/312500000000000000000 : ℝ)*base90 + (2838773/312500000000000000000 : ℝ)*base92 + (2838773/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5899/10000 : ℝ) ≤ (518396154063472999447025810775213/878750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97937/800000000000 : ℝ)*(lower1) + (13597353/20000000000000 : ℝ)*(upper2) + (1305207/20000000000000 : ℝ)*(upper5) + (1509002109793107/50000000000000 : ℝ)*(major0) + (1509002109793107/50000000000000 : ℝ)*(major1) + (1509002109793107/50000000000000 : ℝ)*(major2) + (509772394097481/12500000000000 : ℝ)*(sp0) + (4078129414717121/100000000000000 : ℝ)*(sp1) + (815634330785953/20000000000000 : ℝ)*(sp2) + (969081935964483/50000000000000 : ℝ)*(sp3) + (8052465319/100000000000000 : ℝ)*(sp6) + (355430093/50000000000000 : ℝ)*(sp7) + (25145838981/50000000000000 : ℝ)*(sp9) + (110723047/20000000000000 : ℝ)*(sp12) + (60567643212161/3125000000000 : ℝ)*(f.failure) + (1019544926598771/25000000000000 : ℝ)*(f.sum) + (86035732109049/17575000000000000000000000000 : ℝ)*base65 + (7577206845523991643/1757500000000000000000000000000000 : ℝ)*base68 + (14066601446606491643/1757500000000000000000000000000000 : ℝ)*base70 + (7900982648583991643/1757500000000000000000000000000000 : ℝ)*base72 + (67670851010449/17575000000000000000000000000 : ℝ)*base73 + (20458793571631491643/1757500000000000000000000000000000 : ℝ)*base76 + (17762833813196491643/1757500000000000000000000000000000 : ℝ)*base78 + (22822119057398991643/1757500000000000000000000000000000 : ℝ)*base80 + (30044109812349/17575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (132943/78125000000000000000 : ℝ)*base90 + (132943/78125000000000000000 : ℝ)*base92 + (132943/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80099/100000 : ℝ) ≤ (9512098897575713596571304209907/11875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11831813/50000000000000 : ℝ)*(upper1) + (22534357/25000000000000 : ℝ)*(upper2) + (30207389/100000000000000 : ℝ)*(lower5) + (1664510756003397/50000000000000 : ℝ)*(major0) + (1664510756003397/50000000000000 : ℝ)*(major1) + (1664510756003397/50000000000000 : ℝ)*(major2) + (366413/160000000000 : ℝ)*(sp0) + (12930354813/50000000000000 : ℝ)*(sp1) + (512919273/2500000000000 : ℝ)*(sp3) + (2246720988154431/50000000000000 : ℝ)*(sp8) + (2246708206299613/50000000000000 : ℝ)*(sp9) + (1123360568327213/25000000000000 : ℝ)*(sp10) + (267234950681173/12500000000000 : ℝ)*(sp11) + (13598373/20000000000000 : ℝ)*(sp12) + (133618757638769/6250000000000 : ℝ)*(f.failure) + (1123360568327213/25000000000000 : ℝ)*(f.sum) + (14739401176183/475000000000000000000000000 : ℝ)*base66 + (294414797278605031/47500000000000000000000000000000 : ℝ)*base67 + (531940484328605031/47500000000000000000000000000000 : ℝ)*base69 + (168923242216105031/47500000000000000000000000000000 : ℝ)*base71 + (282952607423/118750000000000000000000000 : ℝ)*base73 + (2208265618894969/47500000000000000000000000000000 : ℝ)*base76 + (1220535009846105031/47500000000000000000000000000000 : ℝ)*base77 + (131491992396105031/47500000000000000000000000000000 : ℝ)*base79 + (821197563279/237500000000000000000000000 : ℝ)*base82 + (97147/156250000000000000000 : ℝ)*base90 + (97147/156250000000000000000 : ℝ)*base92 + (97147/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84449/100000 : ℝ) ≤ (-371037057864162240149586821449359/439375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87546429/100000000000000 : ℝ)*(upper1) + (153147/1000000000000 : ℝ)*(lower2) + (17579013/20000000000000 : ℝ)*(upper3) + (260756803/100000000000000 : ℝ)*(upper5) + (841444436049203/25000000000000 : ℝ)*(major0) + (841444436049203/25000000000000 : ℝ)*(major1) + (841444436049203/25000000000000 : ℝ)*(major2) + (517666173/20000000000000 : ℝ)*(sp4) + (157076193697/100000000000000 : ℝ)*(sp6) + (57142927999/100000000000000 : ℝ)*(sp7) + (574774593754073/12500000000000 : ℝ)*(sp12) + (91963986767269/2000000000000 : ℝ)*(sp13) + (574755282771219/12500000000000 : ℝ)*(sp14) + (135090491205451/6250000000000 : ℝ)*(sp15) + (432301000443043/20000000000000 : ℝ)*(f.failure) + (91963986767269/2000000000000 : ℝ)*(f.sum) + (89150461773083/17575000000000000000000000000 : ℝ)*base66 + (3494939453596116453/878750000000000000000000000000000 : ℝ)*base67 + (5239241567101116453/878750000000000000000000000000000 : ℝ)*base69 + (524771060581383547/878750000000000000000000000000000 : ℝ)*base72 + (675480221973/4393750000000000000000000000 : ℝ)*base73 + (1524203319232633547/878750000000000000000000000000000 : ℝ)*base76 + (3980431046211116453/878750000000000000000000000000000 : ℝ)*base77 + (9762029965831116453/878750000000000000000000000000000 : ℝ)*base79 + (67321309982227/4393750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (122391/500000000000000000000 : ℝ)*base89 + (122391/500000000000000000000 : ℝ)*base91 + (122391/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1367_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5899/10000 : ℝ) else (80099/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84449/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1367_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1367_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5899/10000 : ℝ) else (80099/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84449/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1367_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1367_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1367_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2163/512 : ℝ) ≤ p) (hpb : p ≤ (4327/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38928637/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (14/125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5899/10000 : ℝ) else (80099/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84449/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1367_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
