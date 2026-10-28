-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1057_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:00:12.520586+00:00
-- url     : https://prove2.me/submissions/0ebe0ced-4cd8-4d39-b7f6-add56d721230

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
theorem support_rectangle_w1057_s6_0 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104077703/5000000000 : ℝ)*x 0 + (5395102531/10000000000 : ℝ)*x 1 + (5263731851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104077703/5000000000 : ℝ)^4125 ≤ (13409657514611/100000000000000 : ℝ)^3101 := by
    have hnat : (1104077703 : ℕ)^4125*100000000000000^3101 ≤ 13409657514611^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104077703 5000000000 13409657514611 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395102531/10000000000 : ℝ)^4125 ≤ (275031044311/625000000000 : ℝ)^3101 := by
    have hnat : (5395102531 : ℕ)^4125*625000000000^3101 ≤ 275031044311^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395102531 10000000000 275031044311 625000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263731851/10000000000 : ℝ)^4125 ≤ (21292687687013/50000000000000 : ℝ)^3101 := by
    have hnat : (5263731851 : ℕ)^4125*50000000000000^3101 ≤ 21292687687013^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263731851 10000000000 21292687687013 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104077703/5000000000 : ℝ), (5395102531/10000000000 : ℝ), (5263731851/10000000000 : ℝ)] ![(13409657514611/100000000000000 : ℝ), (275031044311/625000000000 : ℝ), (21292687687013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104077703/5000000000 : ℝ)|^4125 ≤ (13409657514611/100000000000000 : ℝ)^3101
        have hw : |(-1104077703/5000000000 : ℝ)|=(1104077703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395102531/10000000000 : ℝ)|^4125 ≤ (275031044311/625000000000 : ℝ)^3101
        have hw : |(5395102531/10000000000 : ℝ)|=(5395102531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263731851/10000000000 : ℝ)|^4125 ≤ (21292687687013/50000000000000 : ℝ)^3101
        have hw : |(5263731851/10000000000 : ℝ)|=(5263731851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s6_1 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069029259/2000000000 : ℝ)*x 0 + (-1137409797/5000000000 : ℝ)*x 1 + (1315932967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069029259/2000000000 : ℝ)^4125 ≤ (679121550499/1562500000000 : ℝ)^3101 := by
    have hnat : (1069029259 : ℕ)^4125*1562500000000^3101 ≤ 679121550499^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069029259 2000000000 679121550499 1562500000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137409797/5000000000 : ℝ)^4125 ≤ (1395084519687/10000000000000 : ℝ)^3101 := by
    have hnat : (1137409797 : ℕ)^4125*10000000000000^3101 ≤ 1395084519687^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137409797 5000000000 1395084519687 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315932967/2500000000 : ℝ)^4125 ≤ (21292687778489/50000000000000 : ℝ)^3101 := by
    have hnat : (1315932967 : ℕ)^4125*50000000000000^3101 ≤ 21292687778489^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315932967 2500000000 21292687778489 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069029259/2000000000 : ℝ), (-1137409797/5000000000 : ℝ), (1315932967/2500000000 : ℝ)] ![(679121550499/1562500000000 : ℝ), (1395084519687/10000000000000 : ℝ), (21292687778489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069029259/2000000000 : ℝ)|^4125 ≤ (679121550499/1562500000000 : ℝ)^3101
        have hw : |(1069029259/2000000000 : ℝ)|=(1069029259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1137409797/5000000000 : ℝ)|^4125 ≤ (1395084519687/10000000000000 : ℝ)^3101
        have hw : |(-1137409797/5000000000 : ℝ)|=(1137409797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315932967/2500000000 : ℝ)|^4125 ≤ (21292687778489/50000000000000 : ℝ)^3101
        have hw : |(1315932967/2500000000 : ℝ)|=(1315932967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s6_2 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345146101/10000000000 : ℝ)*x 0 + (5263731989/10000000000 : ℝ)*x 1 + (-2274819693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345146101/10000000000 : ℝ)^4125 ≤ (43463777133519/100000000000000 : ℝ)^3101 := by
    have hnat : (5345146101 : ℕ)^4125*100000000000000^3101 ≤ 43463777133519^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345146101 10000000000 43463777133519 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263731989/10000000000 : ℝ)^4125 ≤ (1330793026849/3125000000000 : ℝ)^3101 := by
    have hnat : (5263731989 : ℕ)^4125*3125000000000^3101 ≤ 1330793026849^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263731989 10000000000 1330793026849 3125000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274819693/10000000000 : ℝ)^4125 ≤ (6975423002249/50000000000000 : ℝ)^3101 := by
    have hnat : (2274819693 : ℕ)^4125*50000000000000^3101 ≤ 6975423002249^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274819693 10000000000 6975423002249 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345146101/10000000000 : ℝ), (5263731989/10000000000 : ℝ), (-2274819693/10000000000 : ℝ)] ![(43463777133519/100000000000000 : ℝ), (1330793026849/3125000000000 : ℝ), (6975423002249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345146101/10000000000 : ℝ)|^4125 ≤ (43463777133519/100000000000000 : ℝ)^3101
        have hw : |(5345146101/10000000000 : ℝ)|=(5345146101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263731989/10000000000 : ℝ)|^4125 ≤ (1330793026849/3125000000000 : ℝ)^3101
        have hw : |(5263731989/10000000000 : ℝ)|=(5263731989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2274819693/10000000000 : ℝ)|^4125 ≤ (6975423002249/50000000000000 : ℝ)^3101
        have hw : |(-2274819693/10000000000 : ℝ)|=(2274819693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s6_3 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094189719/2500000000 : ℝ)*x 0 + (4250169871/10000000000 : ℝ)*x 1 + (2253589161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094189719/2500000000 : ℝ)^4125 ≤ (83290498713/250000000000 : ℝ)^3101 := by
    have hnat : (1094189719 : ℕ)^4125*250000000000^3101 ≤ 83290498713^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094189719 2500000000 83290498713 250000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250169871/10000000000 : ℝ)^4125 ≤ (6408111692181/20000000000000 : ℝ)^3101 := by
    have hnat : (4250169871 : ℕ)^4125*20000000000000^3101 ≤ 6408111692181^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250169871 10000000000 6408111692181 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253589161/5000000000 : ℝ)^4125 ≤ (270650328503/781250000000 : ℝ)^3101 := by
    have hnat : (2253589161 : ℕ)^4125*781250000000^3101 ≤ 270650328503^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253589161 5000000000 270650328503 781250000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094189719/2500000000 : ℝ), (4250169871/10000000000 : ℝ), (2253589161/5000000000 : ℝ)] ![(83290498713/250000000000 : ℝ), (6408111692181/20000000000000 : ℝ), (270650328503/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094189719/2500000000 : ℝ)|^4125 ≤ (83290498713/250000000000 : ℝ)^3101
        have hw : |(1094189719/2500000000 : ℝ)|=(1094189719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250169871/10000000000 : ℝ)|^4125 ≤ (6408111692181/20000000000000 : ℝ)^3101
        have hw : |(4250169871/10000000000 : ℝ)|=(4250169871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253589161/5000000000 : ℝ)|^4125 ≤ (270650328503/781250000000 : ℝ)^3101
        have hw : |(2253589161/5000000000 : ℝ)|=(2253589161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s6_4 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208160629/10000000000 : ℝ)*x 0 + (1316015931/2500000000 : ℝ)*x 1 + (2697384727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208160629/10000000000 : ℝ)^4125 ≤ (6704849853321/50000000000000 : ℝ)^3101 := by
    have hnat : (2208160629 : ℕ)^4125*50000000000000^3101 ≤ 6704849853321^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208160629 10000000000 6704849853321 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316015931/2500000000 : ℝ)^4125 ≤ (10647236748723/25000000000000 : ℝ)^3101 := by
    have hnat : (1316015931 : ℕ)^4125*25000000000000^3101 ≤ 10647236748723^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316015931 2500000000 10647236748723 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697384727/5000000000 : ℝ)^4125 ≤ (137504229023/312500000000 : ℝ)^3101 := by
    have hnat : (2697384727 : ℕ)^4125*312500000000^3101 ≤ 137504229023^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697384727 5000000000 137504229023 312500000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208160629/10000000000 : ℝ), (1316015931/2500000000 : ℝ), (2697384727/5000000000 : ℝ)] ![(6704849853321/50000000000000 : ℝ), (10647236748723/25000000000000 : ℝ), (137504229023/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208160629/10000000000 : ℝ)|^4125 ≤ (6704849853321/50000000000000 : ℝ)^3101
        have hw : |(-2208160629/10000000000 : ℝ)|=(2208160629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316015931/2500000000 : ℝ)|^4125 ≤ (10647236748723/25000000000000 : ℝ)^3101
        have hw : |(1316015931/2500000000 : ℝ)|=(1316015931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697384727/5000000000 : ℝ)|^4125 ≤ (137504229023/312500000000 : ℝ)^3101
        have hw : |(2697384727/5000000000 : ℝ)|=(2697384727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s6_5 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42496643/80000000 : ℝ)*x 0 + (-16748297/78125000 : ℝ)*x 1 + (5394769527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42496643/80000000 : ℝ)^4125 ≤ (43106484786973/100000000000000 : ℝ)^3101 := by
    have hnat : (42496643 : ℕ)^4125*100000000000000^3101 ≤ 43106484786973^3101*80000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42496643 80000000 43106484786973 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16748297/78125000 : ℝ)^4125 ≤ (3223040279251/25000000000000 : ℝ)^3101 := by
    have hnat : (16748297 : ℕ)^4125*25000000000000^3101 ≤ 3223040279251^3101*78125000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16748297 78125000 3223040279251 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394769527/10000000000 : ℝ)^4125 ≤ (5500169259923/12500000000000 : ℝ)^3101 := by
    have hnat : (5394769527 : ℕ)^4125*12500000000000^3101 ≤ 5500169259923^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394769527 10000000000 5500169259923 12500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42496643/80000000 : ℝ), (-16748297/78125000 : ℝ), (5394769527/10000000000 : ℝ)] ![(43106484786973/100000000000000 : ℝ), (3223040279251/25000000000000 : ℝ), (5500169259923/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42496643/80000000 : ℝ)|^4125 ≤ (43106484786973/100000000000000 : ℝ)^3101
        have hw : |(42496643/80000000 : ℝ)|=(42496643/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16748297/78125000 : ℝ)|^4125 ≤ (3223040279251/25000000000000 : ℝ)^3101
        have hw : |(-16748297/78125000 : ℝ)|=(16748297/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394769527/10000000000 : ℝ)|^4125 ≤ (5500169259923/12500000000000 : ℝ)^3101
        have hw : |(5394769527/10000000000 : ℝ)|=(5394769527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s6_6 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312080261/10000000000 : ℝ)*x 0 + (269738483/500000000 : ℝ)*x 1 + (-2143781991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312080261/10000000000 : ℝ)^4125 ≤ (43106483556407/100000000000000 : ℝ)^3101 := by
    have hnat : (5312080261 : ℕ)^4125*100000000000000^3101 ≤ 43106483556407^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312080261 10000000000 43106483556407 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269738483/500000000 : ℝ)^4125 ≤ (22000677761193/50000000000000 : ℝ)^3101 := by
    have hnat : (269738483 : ℕ)^4125*50000000000000^3101 ≤ 22000677761193^3101*500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269738483 500000000 22000677761193 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2143781991/10000000000 : ℝ)^4125 ≤ (6446080458507/50000000000000 : ℝ)^3101 := by
    have hnat : (2143781991 : ℕ)^4125*50000000000000^3101 ≤ 6446080458507^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143781991 10000000000 6446080458507 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312080261/10000000000 : ℝ), (269738483/500000000 : ℝ), (-2143781991/10000000000 : ℝ)] ![(43106483556407/100000000000000 : ℝ), (22000677761193/50000000000000 : ℝ), (6446080458507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312080261/10000000000 : ℝ)|^4125 ≤ (43106483556407/100000000000000 : ℝ)^3101
        have hw : |(5312080261/10000000000 : ℝ)|=(5312080261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269738483/500000000 : ℝ)|^4125 ≤ (22000677761193/50000000000000 : ℝ)^3101
        have hw : |(269738483/500000000 : ℝ)|=(269738483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2143781991/10000000000 : ℝ)|^4125 ≤ (6446080458507/50000000000000 : ℝ)^3101
        have hw : |(-2143781991/10000000000 : ℝ)|=(2143781991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s6_7 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188384579/5000000000 : ℝ)*x 0 + (4506529033/10000000000 : ℝ)*x 1 + (850164291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188384579/5000000000 : ℝ)^4125 ≤ (33316303597679/100000000000000 : ℝ)^3101 := by
    have hnat : (2188384579 : ℕ)^4125*100000000000000^3101 ≤ 33316303597679^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188384579 5000000000 33316303597679 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506529033/10000000000 : ℝ)^4125 ≤ (3463660364423/10000000000000 : ℝ)^3101 := by
    have hnat : (4506529033 : ℕ)^4125*10000000000000^3101 ≤ 3463660364423^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506529033 10000000000 3463660364423 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850164291/2000000000 : ℝ)^4125 ≤ (32047092735473/100000000000000 : ℝ)^3101 := by
    have hnat : (850164291 : ℕ)^4125*100000000000000^3101 ≤ 32047092735473^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850164291 2000000000 32047092735473 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188384579/5000000000 : ℝ), (4506529033/10000000000 : ℝ), (850164291/2000000000 : ℝ)] ![(33316303597679/100000000000000 : ℝ), (3463660364423/10000000000000 : ℝ), (32047092735473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188384579/5000000000 : ℝ)|^4125 ≤ (33316303597679/100000000000000 : ℝ)^3101
        have hw : |(2188384579/5000000000 : ℝ)|=(2188384579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506529033/10000000000 : ℝ)|^4125 ≤ (3463660364423/10000000000000 : ℝ)^3101
        have hw : |(4506529033/10000000000 : ℝ)|=(4506529033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850164291/2000000000 : ℝ)|^4125 ≤ (32047092735473/100000000000000 : ℝ)^3101
        have hw : |(850164291/2000000000 : ℝ)|=(850164291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1057_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11227/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1401/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (699/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (699/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (699/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (699/6250 : ℝ) ^ (8249/2048 : ℝ) ≤ (14720045756575683/100000000000000000000 : ℝ) := by
    have hpowers : (699/6250 : ℝ)^8249 ≤ (14720045756575683/100000000000000000000 : ℝ)^2048 := by
      have hnat : (699 : ℕ)^8249*100000000000000000000^2048 ≤ 14720045756575683^2048*6250^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        699 6250 14720045756575683 100000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (699/6250 : ℝ)) (X := (14720045756575683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2811/20000 : ℝ) ^ (8249/2048 : ℝ) ≤ (18474632397463281/50000000000000000000 : ℝ) := by
    have hpowers : (2811/20000 : ℝ)^8249 ≤ (18474632397463281/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2811 : ℕ)^8249*50000000000000000000^2048 ≤ 18474632397463281^2048*20000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 20000 18474632397463281 50000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/20000 : ℝ)) (X := (18474632397463281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014720045756575683/50000000000000000000 : ℝ) ≤ (10000730835699261/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (50014720045756575683/50000000000000000000 : ℝ)^2048 ≤ (10000730835699261/10000000000000000 : ℝ)^8249 := by
      have hnat : (50014720045756575683 : ℕ)^2048*10000000000000000^8249 ≤ 10000730835699261^8249*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014720045756575683 50000000000000000000 10000730835699261 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000730835699261/10000000000000000 : ℝ)) (X := (50014720045756575683/50000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010333862110300449/20000000000000000000 : ℝ) ≤ (5000641278964421/5000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (20010333862110300449/20000000000000000000 : ℝ)^2048 ≤ (5000641278964421/5000000000000000 : ℝ)^8249 := by
      have hnat : (20010333862110300449 : ℕ)^2048*5000000000000000^8249 ≤ 5000641278964421^8249*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010333862110300449 20000000000000000000 5000641278964421 5000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000641278964421/5000000000000000 : ℝ)) (X := (20010333862110300449/20000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018474632397463281/25000000000000000000 : ℝ) ≤ (10001834280158423/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (25018474632397463281/25000000000000000000 : ℝ)^2048 ≤ (10001834280158423/10000000000000000 : ℝ)^8249 := by
      have hnat : (25018474632397463281 : ℕ)^2048*10000000000000000^8249 ≤ 10001834280158423^8249*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018474632397463281 25000000000000000000 10001834280158423 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001834280158423/10000000000000000 : ℝ)) (X := (25018474632397463281/25000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14720045756575683/100000000000000000000 : ℝ) ≤ ((9566585768820436841/9570000000000000000 : ℝ)+2*(551722229581/287100000000000 : ℝ)*(699/6250 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (9566585768820436841/9570000000000000000 : ℝ)+2*(551722229581/287100000000000 : ℝ)*(699/6250 : ℝ)=(10000730835699261/10000000000000000 : ℝ) by norm_num, show 1+2*(14720045756575683/100000000000000000000 : ℝ)=(50014720045756575683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18474632397463281/50000000000000000000 : ℝ)+(14720045756575683/100000000000000000000 : ℝ) ≤ ((9566585768820436841/9570000000000000000 : ℝ)+(551722229581/287100000000000 : ℝ)*((2811/20000 : ℝ)+(699/6250 : ℝ)))^(8249/2048 : ℝ) := by
    rw [show (9566585768820436841/9570000000000000000 : ℝ)+(551722229581/287100000000000 : ℝ)*((2811/20000 : ℝ)+(699/6250 : ℝ))=(5000641278964421/5000000000000000 : ℝ) by norm_num, show 1+(18474632397463281/50000000000000000000 : ℝ)+(14720045756575683/100000000000000000000 : ℝ)=(20010333862110300449/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18474632397463281/50000000000000000000 : ℝ) ≤ ((9566585768820436841/9570000000000000000 : ℝ)+2*(551722229581/287100000000000 : ℝ)*(2811/20000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (9566585768820436841/9570000000000000000 : ℝ)+2*(551722229581/287100000000000 : ℝ)*(2811/20000 : ℝ)=(10001834280158423/10000000000000000 : ℝ) by norm_num, show 1+2*(18474632397463281/50000000000000000000 : ℝ)=(25018474632397463281/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9566585768820436841/9570000000000000000 : ℝ)*(X 1 0+X 2 0)+(551722229581/287100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (9566585768820436841/9570000000000000000 : ℝ)) (alpha := (551722229581/287100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9566585768820436841/9570000000000000000 : ℝ)*(X 0 1+X 2 1)+(551722229581/287100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (9566585768820436841/9570000000000000000 : ℝ)) (alpha := (551722229581/287100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9566585768820436841/9570000000000000000 : ℝ)*(X 0 2+X 1 2)+(551722229581/287100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (699/6250 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (9566585768820436841/9570000000000000000 : ℝ)) (alpha := (551722229581/287100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1104077703/5000000000 : ℝ)*X 0 0+(5395102531/10000000000 : ℝ)*X 0 1+(5263731851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069029259/2000000000 : ℝ)*X 1 0+(-1137409797/5000000000 : ℝ)*X 1 1+(1315932967/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345146101/10000000000 : ℝ)*X 2 0+(5263731989/10000000000 : ℝ)*X 2 1+(-2274819693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094189719/2500000000 : ℝ)*X 0 0+(4250169871/10000000000 : ℝ)*X 0 1+(2253589161/5000000000 : ℝ)*X 0 2+(1094189719/2500000000 : ℝ)*X 1 0+(4250169871/10000000000 : ℝ)*X 1 1+(2253589161/5000000000 : ℝ)*X 1 2+(1094189719/2500000000 : ℝ)*X 2 0+(4250169871/10000000000 : ℝ)*X 2 1+(2253589161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2208160629/10000000000 : ℝ)*X 0 0+(1316015931/2500000000 : ℝ)*X 0 1+(2697384727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42496643/80000000 : ℝ)*X 1 0+(-16748297/78125000 : ℝ)*X 1 1+(5394769527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312080261/10000000000 : ℝ)*X 2 0+(269738483/500000000 : ℝ)*X 2 1+(-2143781991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188384579/5000000000 : ℝ)*X 0 0+(4506529033/10000000000 : ℝ)*X 0 1+(850164291/2000000000 : ℝ)*X 0 2+(2188384579/5000000000 : ℝ)*X 1 0+(4506529033/10000000000 : ℝ)*X 1 1+(850164291/2000000000 : ℝ)*X 1 2+(2188384579/5000000000 : ℝ)*X 2 0+(4506529033/10000000000 : ℝ)*X 2 1+(850164291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (577784567787516354965260383/79750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1597388523/100000000000000 : ℝ)*(base19) + (1288309967/100000000000000 : ℝ)*(base23) + (17531601/100000000000000 : ℝ)*(lower2) + (28530669/10000000000000 : ℝ)*(upper3) + (54938133/100000000000000 : ℝ)*(upper5) + (2875776337866537/50000000000000 : ℝ)*(major0) + (2875776337866537/50000000000000 : ℝ)*(major1) + (2875776337866537/50000000000000 : ℝ)*(major2) + (7612098762155809/100000000000000 : ℝ)*(sp0) + (304485364639629/4000000000000 : ℝ)*(sp1) + (47575840156683/625000000000 : ℝ)*(sp2) + (194547215285861/5000000000000 : ℝ)*(sp3) + (18475611719/50000000000000 : ℝ)*(sp4) + (196022433/781250000000 : ℝ)*(sp7) + (972742349147161/25000000000000 : ℝ)*(f.failure) + (7612135713379247/100000000000000 : ℝ)*(f.sum) + (235816961923/797500000000000000000000000 : ℝ)*base65 + (156585483170096539/159500000000000000000000000000000 : ℝ)*base67 + (1323568067674096539/159500000000000000000000000000000 : ℝ)*base69 + (1153468093872096539/159500000000000000000000000000000 : ℝ)*base71 + (912554943819/398750000000000000000000000 : ℝ)*base73 + (2036409326071403461/159500000000000000000000000000000 : ℝ)*base76 + (410395330774596539/159500000000000000000000000000000 : ℝ)*base77 + (342742382355403461/159500000000000000000000000000000 : ℝ)*base80 + (1558178855633/797500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1233017/625000000000000000000 : ℝ)*base89 + (1233017/625000000000000000000 : ℝ)*base91 + (1233017/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7328355296491307226639/797500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1805147993/100000000000000 : ℝ)*(base19) + (356164239/20000000000000 : ℝ)*(base23) + (122940101/50000000000000 : ℝ)*(upper3) + (56656351/100000000000000 : ℝ)*(lower4) + (197375973/100000000000000 : ℝ)*(upper5) + (5780742912758961/100000000000000 : ℝ)*(major0) + (5780742912758961/100000000000000 : ℝ)*(major1) + (5780742912758961/100000000000000 : ℝ)*(major2) + (1957552261/4000000000000 : ℝ)*(sp1) + (54273675543/100000000000000 : ℝ)*(sp2) + (7650768703909311/100000000000000 : ℝ)*(sp4) + (3825358979977397/50000000000000 : ℝ)*(sp5) + (3825356324706287/50000000000000 : ℝ)*(sp6) + (122209900478227/3125000000000 : ℝ)*(sp7) + (122209900478227/3125000000000 : ℝ)*(f.failure) + (7650768703909311/100000000000000 : ℝ)*(f.sum) + (1827269131407/797500000000000000000000000 : ℝ)*base65 + (1359792960689994067/319000000000000000000000000000000 : ℝ)*base67 + (2574220397967994067/319000000000000000000000000000000 : ℝ)*base69 + (1570693030369005933/319000000000000000000000000000000 : ℝ)*base72 + (1074976575861/1595000000000000000000000000 : ℝ)*base74 + (938192230831994067/319000000000000000000000000000000 : ℝ)*base75 + (701726513577005933/319000000000000000000000000000000 : ℝ)*base78 + (653995248567005933/319000000000000000000000000000000 : ℝ)*base80 + (1707748821721/398750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (44431/78125000000000000000 : ℝ)*base90 + (44431/78125000000000000000 : ℝ)*base92 + (44431/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1057_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1057_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1057_s7_0 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208197577/10000000000 : ℝ)*x 0 + (2697310511/5000000000 : ℝ)*x 1 + (5264185627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208197577/10000000000 : ℝ)^4125 ≤ (6704999089017/50000000000000 : ℝ)^3101 := by
    have hnat : (2208197577 : ℕ)^4125*50000000000000^3101 ≤ 6704999089017^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208197577 10000000000 6704999089017 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697310511/5000000000 : ℝ)^4125 ≤ (43999742860903/100000000000000 : ℝ)^3101 := by
    have hnat : (2697310511 : ℕ)^4125*100000000000000^3101 ≤ 43999742860903^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697310511 5000000000 43999742860903 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264185627/10000000000 : ℝ)^4125 ≤ (42590258934987/100000000000000 : ℝ)^3101 := by
    have hnat : (5264185627 : ℕ)^4125*100000000000000^3101 ≤ 42590258934987^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264185627 10000000000 42590258934987 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208197577/10000000000 : ℝ), (2697310511/5000000000 : ℝ), (5264185627/10000000000 : ℝ)] ![(6704999089017/50000000000000 : ℝ), (43999742860903/100000000000000 : ℝ), (42590258934987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208197577/10000000000 : ℝ)|^4125 ≤ (6704999089017/50000000000000 : ℝ)^3101
        have hw : |(-2208197577/10000000000 : ℝ)|=(2208197577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697310511/5000000000 : ℝ)|^4125 ≤ (43999742860903/100000000000000 : ℝ)^3101
        have hw : |(2697310511/5000000000 : ℝ)|=(2697310511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264185627/10000000000 : ℝ)|^4125 ≤ (42590258934987/100000000000000 : ℝ)^3101
        have hw : |(5264185627/10000000000 : ℝ)|=(5264185627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s7_1 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213801043/400000000 : ℝ)*x 0 + (-2274380077/10000000000 : ℝ)*x 1 + (5264185849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213801043/400000000 : ℝ)^4125 ≤ (10865619716797/25000000000000 : ℝ)^3101 := by
    have hnat : (213801043 : ℕ)^4125*25000000000000^3101 ≤ 10865619716797^3101*400000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213801043 400000000 10865619716797 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274380077/10000000000 : ℝ)^4125 ≤ (6973629898623/50000000000000 : ℝ)^3101 := by
    have hnat : (2274380077 : ℕ)^4125*50000000000000^3101 ≤ 6973629898623^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274380077 10000000000 6973629898623 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264185849/10000000000 : ℝ)^4125 ≤ (42590261324197/100000000000000 : ℝ)^3101 := by
    have hnat : (5264185849 : ℕ)^4125*100000000000000^3101 ≤ 42590261324197^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264185849 10000000000 42590261324197 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213801043/400000000 : ℝ), (-2274380077/10000000000 : ℝ), (5264185849/10000000000 : ℝ)] ![(10865619716797/25000000000000 : ℝ), (6973629898623/50000000000000 : ℝ), (42590261324197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213801043/400000000 : ℝ)|^4125 ≤ (10865619716797/25000000000000 : ℝ)^3101
        have hw : |(213801043/400000000 : ℝ)|=(213801043/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2274380077/10000000000 : ℝ)|^4125 ≤ (6973629898623/50000000000000 : ℝ)^3101
        have hw : |(-2274380077/10000000000 : ℝ)|=(2274380077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264185849/10000000000 : ℝ)|^4125 ≤ (42590261324197/100000000000000 : ℝ)^3101
        have hw : |(5264185849/10000000000 : ℝ)|=(5264185849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s7_2 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672513081/5000000000 : ℝ)*x 0 + (5264185687/10000000000 : ℝ)*x 1 + (-90975207/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672513081/5000000000 : ℝ)^4125 ≤ (1358202494007/3125000000000 : ℝ)^3101 := by
    have hnat : (2672513081 : ℕ)^4125*3125000000000^3101 ≤ 1358202494007^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672513081 5000000000 1358202494007 3125000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264185687/10000000000 : ℝ)^4125 ≤ (42590259580719/100000000000000 : ℝ)^3101 := by
    have hnat : (5264185687 : ℕ)^4125*100000000000000^3101 ≤ 42590259580719^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264185687 10000000000 42590259580719 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90975207/400000000 : ℝ)^4125 ≤ (1743407574583/12500000000000 : ℝ)^3101 := by
    have hnat : (90975207 : ℕ)^4125*12500000000000^3101 ≤ 1743407574583^3101*400000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90975207 400000000 1743407574583 12500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672513081/5000000000 : ℝ), (5264185687/10000000000 : ℝ), (-90975207/400000000 : ℝ)] ![(1358202494007/3125000000000 : ℝ), (42590259580719/100000000000000 : ℝ), (1743407574583/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672513081/5000000000 : ℝ)|^4125 ≤ (1358202494007/3125000000000 : ℝ)^3101
        have hw : |(2672513081/5000000000 : ℝ)|=(2672513081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264185687/10000000000 : ℝ)|^4125 ≤ (42590259580719/100000000000000 : ℝ)^3101
        have hw : |(5264185687/10000000000 : ℝ)|=(5264185687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90975207/400000000 : ℝ)|^4125 ≤ (1743407574583/12500000000000 : ℝ)^3101
        have hw : |(-90975207/400000000 : ℝ)|=(90975207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s7_3 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188391441/5000000000 : ℝ)*x 0 + (4251081911/10000000000 : ℝ)*x 1 + (4506259957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188391441/5000000000 : ℝ)^4125 ≤ (16658221281477/50000000000000 : ℝ)^3101 := by
    have hnat : (2188391441 : ℕ)^4125*50000000000000^3101 ≤ 16658221281477^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188391441 5000000000 16658221281477 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251081911/10000000000 : ℝ)^4125 ≤ (32049704756807/100000000000000 : ℝ)^3101 := by
    have hnat : (4251081911 : ℕ)^4125*100000000000000^3101 ≤ 32049704756807^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251081911 10000000000 32049704756807 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506259957/10000000000 : ℝ)^4125 ≤ (34633852673341/100000000000000 : ℝ)^3101 := by
    have hnat : (4506259957 : ℕ)^4125*100000000000000^3101 ≤ 34633852673341^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506259957 10000000000 34633852673341 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188391441/5000000000 : ℝ), (4251081911/10000000000 : ℝ), (4506259957/10000000000 : ℝ)] ![(16658221281477/50000000000000 : ℝ), (32049704756807/100000000000000 : ℝ), (34633852673341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188391441/5000000000 : ℝ)|^4125 ≤ (16658221281477/50000000000000 : ℝ)^3101
        have hw : |(2188391441/5000000000 : ℝ)|=(2188391441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251081911/10000000000 : ℝ)|^4125 ≤ (32049704756807/100000000000000 : ℝ)^3101
        have hw : |(4251081911/10000000000 : ℝ)|=(4251081911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506259957/10000000000 : ℝ)|^4125 ≤ (34633852673341/100000000000000 : ℝ)^3101
        have hw : |(4506259957/10000000000 : ℝ)|=(4506259957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s7_4 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17665621/80000000 : ℝ)*x 0 + (42116103/80000000 : ℝ)*x 1 + (1348573161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17665621/80000000 : ℝ)^4125 ≤ (13410038956651/100000000000000 : ℝ)^3101 := by
    have hnat : (17665621 : ℕ)^4125*100000000000000^3101 ≤ 13410038956651^3101*80000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17665621 80000000 13410038956651 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42116103/80000000 : ℝ)^4125 ≤ (10648445220323/25000000000000 : ℝ)^3101 := by
    have hnat : (42116103 : ℕ)^4125*25000000000000^3101 ≤ 10648445220323^3101*80000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42116103 80000000 10648445220323 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348573161/2500000000 : ℝ)^4125 ≤ (43996180145977/100000000000000 : ℝ)^3101 := by
    have hnat : (1348573161 : ℕ)^4125*100000000000000^3101 ≤ 43996180145977^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348573161 2500000000 43996180145977 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17665621/80000000 : ℝ), (42116103/80000000 : ℝ), (1348573161/2500000000 : ℝ)] ![(13410038956651/100000000000000 : ℝ), (10648445220323/25000000000000 : ℝ), (43996180145977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17665621/80000000 : ℝ)|^4125 ≤ (13410038956651/100000000000000 : ℝ)^3101
        have hw : |(-17665621/80000000 : ℝ)|=(17665621/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42116103/80000000 : ℝ)|^4125 ≤ (10648445220323/25000000000000 : ℝ)^3101
        have hw : |(42116103/80000000 : ℝ)|=(42116103/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348573161/2500000000 : ℝ)|^4125 ≤ (43996180145977/100000000000000 : ℝ)^3101
        have hw : |(1348573161/2500000000 : ℝ)|=(1348573161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s7_5 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328048961/2500000000 : ℝ)*x 0 + (-67008541/312500000 : ℝ)*x 1 + (1078858477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328048961/2500000000 : ℝ)^4125 ≤ (43107731214757/100000000000000 : ℝ)^3101 := by
    have hnat : (1328048961 : ℕ)^4125*100000000000000^3101 ≤ 43107731214757^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328048961 2500000000 43107731214757 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67008541/312500000 : ℝ)^4125 ≤ (12896091428283/100000000000000 : ℝ)^3101 := by
    have hnat : (67008541 : ℕ)^4125*100000000000000^3101 ≤ 12896091428283^3101*312500000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67008541 312500000 12896091428283 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078858477/2000000000 : ℝ)^4125 ≤ (21998088668001/50000000000000 : ℝ)^3101 := by
    have hnat : (1078858477 : ℕ)^4125*50000000000000^3101 ≤ 21998088668001^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078858477 2000000000 21998088668001 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328048961/2500000000 : ℝ), (-67008541/312500000 : ℝ), (1078858477/2000000000 : ℝ)] ![(43107731214757/100000000000000 : ℝ), (12896091428283/100000000000000 : ℝ), (21998088668001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328048961/2500000000 : ℝ)|^4125 ≤ (43107731214757/100000000000000 : ℝ)^3101
        have hw : |(1328048961/2500000000 : ℝ)|=(1328048961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67008541/312500000 : ℝ)|^4125 ≤ (12896091428283/100000000000000 : ℝ)^3101
        have hw : |(-67008541/312500000 : ℝ)|=(67008541/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078858477/2000000000 : ℝ)|^4125 ≤ (21998088668001/50000000000000 : ℝ)^3101
        have hw : |(1078858477/2000000000 : ℝ)|=(1078858477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s7_6 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83003059/156250000 : ℝ)*x 0 + (1348573131/2500000000 : ℝ)*x 1 + (-33504269/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83003059/156250000 : ℝ)^4125 ≤ (4310773048073/10000000000000 : ℝ)^3101 := by
    have hnat : (83003059 : ℕ)^4125*10000000000000^3101 ≤ 4310773048073^3101*156250000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83003059 156250000 4310773048073 10000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348573131/2500000000 : ℝ)^4125 ≤ (21998089422029/50000000000000 : ℝ)^3101 := by
    have hnat : (1348573131 : ℕ)^4125*50000000000000^3101 ≤ 21998089422029^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348573131 2500000000 21998089422029 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33504269/156250000 : ℝ)^4125 ≤ (2579218132053/20000000000000 : ℝ)^3101 := by
    have hnat : (33504269 : ℕ)^4125*20000000000000^3101 ≤ 2579218132053^3101*156250000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33504269 156250000 2579218132053 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83003059/156250000 : ℝ), (1348573131/2500000000 : ℝ), (-33504269/156250000 : ℝ)] ![(4310773048073/10000000000000 : ℝ), (21998089422029/50000000000000 : ℝ), (2579218132053/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83003059/156250000 : ℝ)|^4125 ≤ (4310773048073/10000000000000 : ℝ)^3101
        have hw : |(83003059/156250000 : ℝ)|=(83003059/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348573131/2500000000 : ℝ)|^4125 ≤ (21998089422029/50000000000000 : ℝ)^3101
        have hw : |(1348573131/2500000000 : ℝ)|=(1348573131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33504269/156250000 : ℝ)|^4125 ≤ (2579218132053/20000000000000 : ℝ)^3101
        have hw : |(-33504269/156250000 : ℝ)|=(33504269/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s7_7 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188396249/5000000000 : ℝ)*x 0 + (2252810207/5000000000 : ℝ)*x 1 + (4251724143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188396249/5000000000 : ℝ)^4125 ≤ (33316539931889/100000000000000 : ℝ)^3101 := by
    have hnat : (2188396249 : ℕ)^4125*100000000000000^3101 ≤ 33316539931889^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188396249 5000000000 33316539931889 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252810207/5000000000 : ℝ)^4125 ≤ (1082103573471/3125000000000 : ℝ)^3101 := by
    have hnat : (2252810207 : ℕ)^4125*3125000000000^3101 ≤ 1082103573471^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252810207 5000000000 1082103573471 3125000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251724143/10000000000 : ℝ)^4125 ≤ (801403642519/2500000000000 : ℝ)^3101 := by
    have hnat : (4251724143 : ℕ)^4125*2500000000000^3101 ≤ 801403642519^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251724143 10000000000 801403642519 2500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188396249/5000000000 : ℝ), (2252810207/5000000000 : ℝ), (4251724143/10000000000 : ℝ)] ![(33316539931889/100000000000000 : ℝ), (1082103573471/3125000000000 : ℝ), (801403642519/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188396249/5000000000 : ℝ)|^4125 ≤ (33316539931889/100000000000000 : ℝ)^3101
        have hw : |(2188396249/5000000000 : ℝ)|=(2188396249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252810207/5000000000 : ℝ)|^4125 ≤ (1082103573471/3125000000000 : ℝ)^3101
        have hw : |(2252810207/5000000000 : ℝ)|=(2252810207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251724143/10000000000 : ℝ)|^4125 ≤ (801403642519/2500000000000 : ℝ)^3101
        have hw : |(4251724143/10000000000 : ℝ)|=(4251724143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1057_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11237/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7/50 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11227/100000 : ℝ) ^ (8249/2048 : ℝ) ≤ (14949332477463823/100000000000000000000 : ℝ) := by
    have hpowers : (11227/100000 : ℝ)^8249 ≤ (14949332477463823/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11227 : ℕ)^8249*100000000000000000000^2048 ≤ 14949332477463823^2048*100000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11227 100000 14949332477463823 100000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11227/100000 : ℝ)) (X := (14949332477463823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1401/10000 : ℝ) ^ (8249/2048 : ℝ) ≤ (36475073915596351/100000000000000000000 : ℝ) := by
    have hpowers : (1401/10000 : ℝ)^8249 ≤ (36475073915596351/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1401 : ℕ)^8249*100000000000000000000^2048 ≤ 36475073915596351^2048*10000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 10000 36475073915596351 100000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/10000 : ℝ)) (X := (36475073915596351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014949332477463823/50000000000000000000 : ℝ) ≤ (1250092777284871/1250000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (50014949332477463823/50000000000000000000 : ℝ)^2048 ≤ (1250092777284871/1250000000000000 : ℝ)^8249 := by
      have hnat : (50014949332477463823 : ℕ)^2048*1250000000000000^8249 ≤ 1250092777284871^8249*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014949332477463823 50000000000000000000 1250092777284871 1250000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250092777284871/1250000000000000 : ℝ)) (X := (50014949332477463823/50000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025712203196530087/50000000000000000000 : ℝ) ≤ (10001276479986639/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (50025712203196530087/50000000000000000000 : ℝ)^2048 ≤ (10001276479986639/10000000000000000 : ℝ)^8249 := by
      have hnat : (50025712203196530087 : ℕ)^2048*10000000000000000^8249 ≤ 10001276479986639^8249*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025712203196530087 50000000000000000000 10001276479986639 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001276479986639/10000000000000000 : ℝ)) (X := (50025712203196530087/50000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036475073915596351/50000000000000000000 : ℝ) ≤ (1000181074169431/1000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (50036475073915596351/50000000000000000000 : ℝ)^2048 ≤ (1000181074169431/1000000000000000 : ℝ)^8249 := by
      have hnat : (50036475073915596351 : ℕ)^2048*1000000000000000^8249 ≤ 1000181074169431^8249*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036475073915596351 50000000000000000000 1000181074169431 1000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000181074169431/1000000000000000 : ℝ)) (X := (50036475073915596351/50000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14949332477463823/100000000000000000000 : ℝ) ≤ ((2782006928108632331/2783000000000000000 : ℝ)+2*(534261707671/278300000000000 : ℝ)*(11227/100000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (2782006928108632331/2783000000000000000 : ℝ)+2*(534261707671/278300000000000 : ℝ)*(11227/100000 : ℝ)=(1250092777284871/1250000000000000 : ℝ) by norm_num, show 1+2*(14949332477463823/100000000000000000000 : ℝ)=(50014949332477463823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36475073915596351/100000000000000000000 : ℝ)+(14949332477463823/100000000000000000000 : ℝ) ≤ ((2782006928108632331/2783000000000000000 : ℝ)+(534261707671/278300000000000 : ℝ)*((1401/10000 : ℝ)+(11227/100000 : ℝ)))^(8249/2048 : ℝ) := by
    rw [show (2782006928108632331/2783000000000000000 : ℝ)+(534261707671/278300000000000 : ℝ)*((1401/10000 : ℝ)+(11227/100000 : ℝ))=(10001276479986639/10000000000000000 : ℝ) by norm_num, show 1+(36475073915596351/100000000000000000000 : ℝ)+(14949332477463823/100000000000000000000 : ℝ)=(50025712203196530087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36475073915596351/100000000000000000000 : ℝ) ≤ ((2782006928108632331/2783000000000000000 : ℝ)+2*(534261707671/278300000000000 : ℝ)*(1401/10000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (2782006928108632331/2783000000000000000 : ℝ)+2*(534261707671/278300000000000 : ℝ)*(1401/10000 : ℝ)=(1000181074169431/1000000000000000 : ℝ) by norm_num, show 1+2*(36475073915596351/100000000000000000000 : ℝ)=(50036475073915596351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2782006928108632331/2783000000000000000 : ℝ)*(X 1 0+X 2 0)+(534261707671/278300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (2782006928108632331/2783000000000000000 : ℝ)) (alpha := (534261707671/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2782006928108632331/2783000000000000000 : ℝ)*(X 0 1+X 2 1)+(534261707671/278300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (2782006928108632331/2783000000000000000 : ℝ)) (alpha := (534261707671/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2782006928108632331/2783000000000000000 : ℝ)*(X 0 2+X 1 2)+(534261707671/278300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (2782006928108632331/2783000000000000000 : ℝ)) (alpha := (534261707671/278300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2208197577/10000000000 : ℝ)*X 0 0+(2697310511/5000000000 : ℝ)*X 0 1+(5264185627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213801043/400000000 : ℝ)*X 1 0+(-2274380077/10000000000 : ℝ)*X 1 1+(5264185849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672513081/5000000000 : ℝ)*X 2 0+(5264185687/10000000000 : ℝ)*X 2 1+(-90975207/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188391441/5000000000 : ℝ)*X 0 0+(4251081911/10000000000 : ℝ)*X 0 1+(4506259957/10000000000 : ℝ)*X 0 2+(2188391441/5000000000 : ℝ)*X 1 0+(4251081911/10000000000 : ℝ)*X 1 1+(4506259957/10000000000 : ℝ)*X 1 2+(2188391441/5000000000 : ℝ)*X 2 0+(4251081911/10000000000 : ℝ)*X 2 1+(4506259957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17665621/80000000 : ℝ)*X 0 0+(42116103/80000000 : ℝ)*X 0 1+(1348573161/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328048961/2500000000 : ℝ)*X 1 0+(-67008541/312500000 : ℝ)*X 1 1+(1078858477/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83003059/156250000 : ℝ)*X 2 0+(1348573131/2500000000 : ℝ)*X 2 1+(-33504269/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188396249/5000000000 : ℝ)*X 0 0+(2252810207/5000000000 : ℝ)*X 0 1+(4251724143/10000000000 : ℝ)*X 0 2+(2188396249/5000000000 : ℝ)*X 1 0+(2252810207/5000000000 : ℝ)*X 1 1+(4251724143/10000000000 : ℝ)*X 1 2+(2188396249/5000000000 : ℝ)*X 2 0+(2252810207/5000000000 : ℝ)*X 2 1+(4251724143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97341677397941904367461789/27830000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040897043/100000000000000 : ℝ)*(base19) + (1056113123/100000000000000 : ℝ)*(base23) + (228078637/100000000000000 : ℝ)*(upper3) + (58567283/100000000000000 : ℝ)*(upper4) + (9107207/50000000000000 : ℝ)*(upper5) + (1158556697594173/20000000000000 : ℝ)*(major0) + (1158556697594173/20000000000000 : ℝ)*(major1) + (1158556697594173/20000000000000 : ℝ)*(major2) + (7666671063255183/100000000000000 : ℝ)*(sp0) + (958337932735507/12500000000000 : ℝ)*(sp1) + (306668137866719/4000000000000 : ℝ)*(sp2) + (391884463694699/10000000000000 : ℝ)*(sp3) + (8359881479/25000000000000 : ℝ)*(sp4) + (4429905703/25000000000000 : ℝ)*(sp7) + (3918862356569801/100000000000000 : ℝ)*(f.failure) + (7666704502781099/100000000000000 : ℝ)*(f.sum) + (2897233334253/695750000000000000000000000 : ℝ)*base66 + (556457867009602737/55660000000000000000000000000000 : ℝ)*base68 + (65373504124777263/55660000000000000000000000000000 : ℝ)*base69 + (128948157696877263/55660000000000000000000000000000 : ℝ)*base71 + (2043472636407/556600000000000000000000000 : ℝ)*base74 + (422536873873562737/55660000000000000000000000000000 : ℝ)*base76 + (992923767708122737/55660000000000000000000000000000 : ℝ)*base78 + (66418783331942737/55660000000000000000000000000000 : ℝ)*base80 + (583699850053/139150000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16345097/2500000000000000000000 : ℝ)*base89 + (16345097/2500000000000000000000 : ℝ)*base91 + (16345097/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (635042586282962369578955529/69575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2133807953/100000000000000 : ℝ)*(base19) + (1179211459/50000000000000 : ℝ)*(base23) + (7490081/6250000000000 : ℝ)*(upper2) + (190522759/100000000000000 : ℝ)*(upper3) + (79745769/100000000000000 : ℝ)*(upper5) + (2910992505348549/50000000000000 : ℝ)*(major0) + (2910992505348549/50000000000000 : ℝ)*(major1) + (2910992505348549/50000000000000 : ℝ)*(major2) + (45553297229/100000000000000 : ℝ)*(sp1) + (1533849447/2500000000000 : ℝ)*(sp2) + (7705352306998671/100000000000000 : ℝ)*(sp4) + (481581538743343/6250000000000 : ℝ)*(sp5) + (7705288594597873/100000000000000 : ℝ)*(sp6) + (492327176268383/12500000000000 : ℝ)*(sp7) + (492327176268383/12500000000000 : ℝ)*(f.failure) + (7705352306998671/100000000000000 : ℝ)*(f.sum) + (3327850686997/13915000000000000000000000000 : ℝ)*base66 + (1329644538676977719/139150000000000000000000000000000 : ℝ)*base67 + (469629542333727719/139150000000000000000000000000000 : ℝ)*base69 + (26437676910277719/139150000000000000000000000000000 : ℝ)*base71 + (69246512117353/13915000000000000000000000000 : ℝ)*base73 + (1954481773954177719/139150000000000000000000000000000 : ℝ)*base75 + (1302168917687127719/139150000000000000000000000000000 : ℝ)*base77 + (851884718000927719/139150000000000000000000000000000 : ℝ)*base79 + (8451214553699/6957500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (481649/312500000000000000000 : ℝ)*base90 + (481649/312500000000000000000 : ℝ)*base92 + (481649/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1057_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7/50 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1057_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1057_s8_0 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208205311/10000000000 : ℝ)*x 0 + (1348628479/2500000000 : ℝ)*x 1 + (5264287797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208205311/10000000000 : ℝ)^4125 ≤ (3352515163659/25000000000000 : ℝ)^3101 := by
    have hnat : (2208205311 : ℕ)^4125*25000000000000^3101 ≤ 3352515163659^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208205311 10000000000 3352515163659 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348628479/2500000000 : ℝ)^4125 ≤ (21999290406861/50000000000000 : ℝ)^3101 := by
    have hnat : (1348628479 : ℕ)^4125*50000000000000^3101 ≤ 21999290406861^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348628479 2500000000 21999290406861 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264287797/10000000000 : ℝ)^4125 ≤ (1703654340521/4000000000000 : ℝ)^3101 := by
    have hnat : (5264287797 : ℕ)^4125*4000000000000^3101 ≤ 1703654340521^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264287797 10000000000 1703654340521 4000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208205311/10000000000 : ℝ), (1348628479/2500000000 : ℝ), (5264287797/10000000000 : ℝ)] ![(3352515163659/25000000000000 : ℝ), (21999290406861/50000000000000 : ℝ), (1703654340521/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208205311/10000000000 : ℝ)|^4125 ≤ (3352515163659/25000000000000 : ℝ)^3101
        have hw : |(-2208205311/10000000000 : ℝ)|=(2208205311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348628479/2500000000 : ℝ)|^4125 ≤ (21999290406861/50000000000000 : ℝ)^3101
        have hw : |(1348628479/2500000000 : ℝ)|=(1348628479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264287797/10000000000 : ℝ)|^4125 ≤ (1703654340521/4000000000000 : ℝ)^3101
        have hw : |(5264287797/10000000000 : ℝ)|=(5264287797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s8_1 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068999967/2000000000 : ℝ)*x 0 + (-2274280351/10000000000 : ℝ)*x 1 + (5264287809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068999967/2000000000 : ℝ)^4125 ≤ (8692439008479/20000000000000 : ℝ)^3101 := by
    have hnat : (1068999967 : ℕ)^4125*20000000000000^3101 ≤ 8692439008479^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068999967 2000000000 8692439008479 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274280351/10000000000 : ℝ)^4125 ≤ (6973223152619/50000000000000 : ℝ)^3101 := by
    have hnat : (2274280351 : ℕ)^4125*50000000000000^3101 ≤ 6973223152619^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274280351 10000000000 6973223152619 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264287809/10000000000 : ℝ)^4125 ≤ (10647839660543/25000000000000 : ℝ)^3101 := by
    have hnat : (5264287809 : ℕ)^4125*25000000000000^3101 ≤ 10647839660543^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264287809 10000000000 10647839660543 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068999967/2000000000 : ℝ), (-2274280351/10000000000 : ℝ), (5264287809/10000000000 : ℝ)] ![(8692439008479/20000000000000 : ℝ), (6973223152619/50000000000000 : ℝ), (10647839660543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068999967/2000000000 : ℝ)|^4125 ≤ (8692439008479/20000000000000 : ℝ)^3101
        have hw : |(1068999967/2000000000 : ℝ)|=(1068999967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2274280351/10000000000 : ℝ)|^4125 ≤ (6973223152619/50000000000000 : ℝ)^3101
        have hw : |(-2274280351/10000000000 : ℝ)|=(2274280351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264287809/10000000000 : ℝ)|^4125 ≤ (10647839660543/25000000000000 : ℝ)^3101
        have hw : |(5264287809/10000000000 : ℝ)|=(5264287809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s8_2 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344999813/10000000000 : ℝ)*x 0 + (5264287811/10000000000 : ℝ)*x 1 + (-284285047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344999813/10000000000 : ℝ)^4125 ≤ (43462194804433/100000000000000 : ℝ)^3101 := by
    have hnat : (5344999813 : ℕ)^4125*100000000000000^3101 ≤ 43462194804433^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344999813 10000000000 43462194804433 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264287811/10000000000 : ℝ)^4125 ≤ (42591358663697/100000000000000 : ℝ)^3101 := by
    have hnat : (5264287811 : ℕ)^4125*100000000000000^3101 ≤ 42591358663697^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264287811 10000000000 42591358663697 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284285047/1250000000 : ℝ)^4125 ≤ (871652906823/6250000000000 : ℝ)^3101 := by
    have hnat : (284285047 : ℕ)^4125*6250000000000^3101 ≤ 871652906823^3101*1250000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284285047 1250000000 871652906823 6250000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344999813/10000000000 : ℝ), (5264287811/10000000000 : ℝ), (-284285047/1250000000 : ℝ)] ![(43462194804433/100000000000000 : ℝ), (42591358663697/100000000000000 : ℝ), (871652906823/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344999813/10000000000 : ℝ)|^4125 ≤ (43462194804433/100000000000000 : ℝ)^3101
        have hw : |(5344999813/10000000000 : ℝ)|=(5344999813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264287811/10000000000 : ℝ)|^4125 ≤ (42591358663697/100000000000000 : ℝ)^3101
        have hw : |(5264287811/10000000000 : ℝ)|=(5264287811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284285047/1250000000 : ℝ)|^4125 ≤ (871652906823/6250000000000 : ℝ)^3101
        have hw : |(-284285047/1250000000 : ℝ)|=(284285047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s8_3 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875357637/2000000000 : ℝ)*x 0 + (2125642843/5000000000 : ℝ)*x 1 + (450605481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875357637/2000000000 : ℝ)^4125 ≤ (6663299251929/20000000000000 : ℝ)^3101 := by
    have hnat : (875357637 : ℕ)^4125*20000000000000^3101 ≤ 6663299251929^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875357637 2000000000 6663299251929 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125642843/5000000000 : ℝ)^4125 ≤ (32051748381237/100000000000000 : ℝ)^3101 := by
    have hnat : (2125642843 : ℕ)^4125*100000000000000^3101 ≤ 32051748381237^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125642843 5000000000 32051748381237 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450605481/1000000000 : ℝ)^4125 ≤ (8657938833557/25000000000000 : ℝ)^3101 := by
    have hnat : (450605481 : ℕ)^4125*25000000000000^3101 ≤ 8657938833557^3101*1000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450605481 1000000000 8657938833557 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875357637/2000000000 : ℝ), (2125642843/5000000000 : ℝ), (450605481/1000000000 : ℝ)] ![(6663299251929/20000000000000 : ℝ), (32051748381237/100000000000000 : ℝ), (8657938833557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875357637/2000000000 : ℝ)|^4125 ≤ (6663299251929/20000000000000 : ℝ)^3101
        have hw : |(875357637/2000000000 : ℝ)|=(875357637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125642843/5000000000 : ℝ)|^4125 ≤ (32051748381237/100000000000000 : ℝ)^3101
        have hw : |(2125642843/5000000000 : ℝ)|=(2125642843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450605481/1000000000 : ℝ)|^4125 ≤ (8657938833557/25000000000000 : ℝ)^3101
        have hw : |(450605481/1000000000 : ℝ)|=(450605481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s8_4 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55205259/250000000 : ℝ)*x 0 + (5264613839/10000000000 : ℝ)*x 1 + (5394186729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55205259/250000000 : ℝ)^4125 ≤ (13410101441377/100000000000000 : ℝ)^3101 := by
    have hnat : (55205259 : ℕ)^4125*100000000000000^3101 ≤ 13410101441377^3101*250000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55205259 250000000 13410101441377 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264613839/10000000000 : ℝ)^4125 ≤ (42594867502333/100000000000000 : ℝ)^3101 := by
    have hnat : (5264613839 : ℕ)^4125*100000000000000^3101 ≤ 42594867502333^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264613839 10000000000 42594867502333 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394186729/10000000000 : ℝ)^4125 ≤ (8799006208723/20000000000000 : ℝ)^3101 := by
    have hnat : (5394186729 : ℕ)^4125*20000000000000^3101 ≤ 8799006208723^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394186729 10000000000 8799006208723 20000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55205259/250000000 : ℝ), (5264613839/10000000000 : ℝ), (5394186729/10000000000 : ℝ)] ![(13410101441377/100000000000000 : ℝ), (42594867502333/100000000000000 : ℝ), (8799006208723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55205259/250000000 : ℝ)|^4125 ≤ (13410101441377/100000000000000 : ℝ)^3101
        have hw : |(-55205259/250000000 : ℝ)|=(55205259/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264613839/10000000000 : ℝ)|^4125 ≤ (42594867502333/100000000000000 : ℝ)^3101
        have hw : |(5264613839/10000000000 : ℝ)|=(5264613839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394186729/10000000000 : ℝ)|^4125 ≤ (8799006208723/20000000000000 : ℝ)^3101
        have hw : |(5394186729/10000000000 : ℝ)|=(5394186729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s8_5 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656110977/5000000000 : ℝ)*x 0 + (-2144381487/10000000000 : ℝ)*x 1 + (5394186639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656110977/5000000000 : ℝ)^4125 ≤ (5388501632483/12500000000000 : ℝ)^3101 := by
    have hnat : (2656110977 : ℕ)^4125*12500000000000^3101 ≤ 5388501632483^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656110977 5000000000 5388501632483 12500000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144381487/10000000000 : ℝ)^4125 ≤ (12896956855743/100000000000000 : ℝ)^3101 := by
    have hnat : (2144381487 : ℕ)^4125*100000000000000^3101 ≤ 12896956855743^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144381487 10000000000 12896956855743 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394186639/10000000000 : ℝ)^4125 ≤ (21997515033591/50000000000000 : ℝ)^3101 := by
    have hnat : (5394186639 : ℕ)^4125*50000000000000^3101 ≤ 21997515033591^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394186639 10000000000 21997515033591 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656110977/5000000000 : ℝ), (-2144381487/10000000000 : ℝ), (5394186639/10000000000 : ℝ)] ![(5388501632483/12500000000000 : ℝ), (12896956855743/100000000000000 : ℝ), (21997515033591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656110977/5000000000 : ℝ)|^4125 ≤ (5388501632483/12500000000000 : ℝ)^3101
        have hw : |(2656110977/5000000000 : ℝ)|=(2656110977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144381487/10000000000 : ℝ)|^4125 ≤ (12896956855743/100000000000000 : ℝ)^3101
        have hw : |(-2144381487/10000000000 : ℝ)|=(2144381487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394186639/10000000000 : ℝ)|^4125 ≤ (21997515033591/50000000000000 : ℝ)^3101
        have hw : |(5394186639/10000000000 : ℝ)|=(5394186639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s8_6 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312221933/10000000000 : ℝ)*x 0 + (2697093293/5000000000 : ℝ)*x 1 + (-536095397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312221933/10000000000 : ℝ)^4125 ≤ (43108012833179/100000000000000 : ℝ)^3101 := by
    have hnat : (5312221933 : ℕ)^4125*100000000000000^3101 ≤ 43108012833179^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312221933 10000000000 43108012833179 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697093293/5000000000 : ℝ)^4125 ≤ (10998757373043/25000000000000 : ℝ)^3101 := by
    have hnat : (2697093293 : ℕ)^4125*25000000000000^3101 ≤ 10998757373043^3101*5000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697093293 5000000000 10998757373043 25000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536095397/2500000000 : ℝ)^4125 ≤ (515878306551/4000000000000 : ℝ)^3101 := by
    have hnat : (536095397 : ℕ)^4125*4000000000000^3101 ≤ 515878306551^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536095397 2500000000 515878306551 4000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312221933/10000000000 : ℝ), (2697093293/5000000000 : ℝ), (-536095397/2500000000 : ℝ)] ![(43108012833179/100000000000000 : ℝ), (10998757373043/25000000000000 : ℝ), (515878306551/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312221933/10000000000 : ℝ)|^4125 ≤ (43108012833179/100000000000000 : ℝ)^3101
        have hw : |(5312221933/10000000000 : ℝ)|=(5312221933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697093293/5000000000 : ℝ)|^4125 ≤ (10998757373043/25000000000000 : ℝ)^3101
        have hw : |(2697093293/5000000000 : ℝ)|=(2697093293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536095397/2500000000 : ℝ)|^4125 ≤ (515878306551/4000000000000 : ℝ)^3101
        have hw : |(-536095397/2500000000 : ℝ)|=(536095397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1057_s8_7 (p : ℝ) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875359577/2000000000 : ℝ)*x 0 + (1126354267/2500000000 : ℝ)*x 1 + (4251925979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875359577/2000000000 : ℝ)^4125 ≤ (33316594479179/100000000000000 : ℝ)^3101 := by
    have hnat : (875359577 : ℕ)^4125*100000000000000^3101 ≤ 33316594479179^3101*2000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875359577 2000000000 33316594479179 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126354267/2500000000 : ℝ)^4125 ≤ (17312617760973/50000000000000 : ℝ)^3101 := by
    have hnat : (1126354267 : ℕ)^4125*50000000000000^3101 ≤ 17312617760973^3101*2500000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126354267 2500000000 17312617760973 50000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251925979/10000000000 : ℝ)^4125 ≤ (32058169980113/100000000000000 : ℝ)^3101 := by
    have hnat : (4251925979 : ℕ)^4125*100000000000000^3101 ≤ 32058169980113^3101*10000000000^4125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251925979 10000000000 32058169980113 100000000000000 4125 3101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4125/1024 : ℝ)) 4125 3101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875359577/2000000000 : ℝ), (1126354267/2500000000 : ℝ), (4251925979/10000000000 : ℝ)] ![(33316594479179/100000000000000 : ℝ), (17312617760973/50000000000000 : ℝ), (32058169980113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875359577/2000000000 : ℝ)|^4125 ≤ (33316594479179/100000000000000 : ℝ)^3101
        have hw : |(875359577/2000000000 : ℝ)|=(875359577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126354267/2500000000 : ℝ)|^4125 ≤ (17312617760973/50000000000000 : ℝ)^3101
        have hw : |(1126354267/2500000000 : ℝ)|=(1126354267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251925979/10000000000 : ℝ)|^4125 ≤ (32058169980113/100000000000000 : ℝ)^3101
        have hw : |(4251925979/10000000000 : ℝ)|=(4251925979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1057_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11239/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13997/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11237/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11237/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11237/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11237/100000 : ℝ) ^ (8249/2048 : ℝ) ≤ (7501518756971527/50000000000000000000 : ℝ) := by
    have hpowers : (11237/100000 : ℝ)^8249 ≤ (7501518756971527/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11237 : ℕ)^8249*50000000000000000000^2048 ≤ 7501518756971527^2048*100000^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11237 100000 7501518756971527 50000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11237/100000 : ℝ)) (X := (7501518756971527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7/50 : ℝ) ^ (8249/2048 : ℝ) ≤ (7274064491718313/20000000000000000000 : ℝ) := by
    have hpowers : (7/50 : ℝ)^8249 ≤ (7274064491718313/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7 : ℕ)^8249*20000000000000000000^2048 ≤ 7274064491718313^2048*50^8249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 50 7274064491718313 20000000000000000000 8249 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/50 : ℝ)) (X := (7274064491718313/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007501518756971527/25000000000000000000 : ℝ) ≤ (10000744884375617/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (25007501518756971527/25000000000000000000 : ℝ)^2048 ≤ (10000744884375617/10000000000000000 : ℝ)^8249 := by
      have hnat : (25007501518756971527 : ℕ)^2048*10000000000000000^8249 ≤ 10000744884375617^8249*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007501518756971527 25000000000000000000 10000744884375617 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000744884375617/10000000000000000 : ℝ)) (X := (25007501518756971527/25000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051373359972534619/100000000000000000000 : ℝ) ≤ (5000637606566879/5000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (100051373359972534619/100000000000000000000 : ℝ)^2048 ≤ (5000637606566879/5000000000000000 : ℝ)^8249 := by
      have hnat : (100051373359972534619 : ℕ)^2048*5000000000000000^8249 ≤ 5000637606566879^8249*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051373359972534619 100000000000000000000 5000637606566879 5000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000637606566879/5000000000000000 : ℝ)) (X := (100051373359972534619/100000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007274064491718313/10000000000000000000 : ℝ) ≤ (10001805541891899/10000000000000000 : ℝ) ^ (8249/2048 : ℝ) := by
    have hpowers : (10007274064491718313/10000000000000000000 : ℝ)^2048 ≤ (10001805541891899/10000000000000000 : ℝ)^8249 := by
      have hnat : (10007274064491718313 : ℕ)^2048*10000000000000000^8249 ≤ 10001805541891899^8249*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007274064491718313 10000000000000000000 10001805541891899 10000000000000000 2048 8249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001805541891899/10000000000000000 : ℝ)) (X := (10007274064491718313/10000000000000000000 : ℝ)) (by norm_num) 8249 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7501518756971527/50000000000000000000 : ℝ) ≤ ((27620139507019368937/27630000000000000000 : ℝ)+2*(530328758141/276300000000000 : ℝ)*(11237/100000 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (27620139507019368937/27630000000000000000 : ℝ)+2*(530328758141/276300000000000 : ℝ)*(11237/100000 : ℝ)=(10000744884375617/10000000000000000 : ℝ) by norm_num, show 1+2*(7501518756971527/50000000000000000000 : ℝ)=(25007501518756971527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7274064491718313/20000000000000000000 : ℝ)+(7501518756971527/50000000000000000000 : ℝ) ≤ ((27620139507019368937/27630000000000000000 : ℝ)+(530328758141/276300000000000 : ℝ)*((7/50 : ℝ)+(11237/100000 : ℝ)))^(8249/2048 : ℝ) := by
    rw [show (27620139507019368937/27630000000000000000 : ℝ)+(530328758141/276300000000000 : ℝ)*((7/50 : ℝ)+(11237/100000 : ℝ))=(5000637606566879/5000000000000000 : ℝ) by norm_num, show 1+(7274064491718313/20000000000000000000 : ℝ)+(7501518756971527/50000000000000000000 : ℝ)=(100051373359972534619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7274064491718313/20000000000000000000 : ℝ) ≤ ((27620139507019368937/27630000000000000000 : ℝ)+2*(530328758141/276300000000000 : ℝ)*(7/50 : ℝ))^(8249/2048 : ℝ) := by
    rw [show (27620139507019368937/27630000000000000000 : ℝ)+2*(530328758141/276300000000000 : ℝ)*(7/50 : ℝ)=(10001805541891899/10000000000000000 : ℝ) by norm_num, show 1+2*(7274064491718313/20000000000000000000 : ℝ)=(10007274064491718313/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27620139507019368937/27630000000000000000 : ℝ)*(X 1 0+X 2 0)+(530328758141/276300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7/50 : ℝ)) (c := (27620139507019368937/27630000000000000000 : ℝ)) (alpha := (530328758141/276300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27620139507019368937/27630000000000000000 : ℝ)*(X 0 1+X 2 1)+(530328758141/276300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7/50 : ℝ)) (c := (27620139507019368937/27630000000000000000 : ℝ)) (alpha := (530328758141/276300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27620139507019368937/27630000000000000000 : ℝ)*(X 0 2+X 1 2)+(530328758141/276300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8249/2048 : ℝ)) (lo := (11237/100000 : ℝ)) (hi := (7/50 : ℝ)) (c := (27620139507019368937/27630000000000000000 : ℝ)) (alpha := (530328758141/276300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2208205311/10000000000 : ℝ)*X 0 0+(1348628479/2500000000 : ℝ)*X 0 1+(5264287797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068999967/2000000000 : ℝ)*X 1 0+(-2274280351/10000000000 : ℝ)*X 1 1+(5264287809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344999813/10000000000 : ℝ)*X 2 0+(5264287811/10000000000 : ℝ)*X 2 1+(-284285047/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875357637/2000000000 : ℝ)*X 0 0+(2125642843/5000000000 : ℝ)*X 0 1+(450605481/1000000000 : ℝ)*X 0 2+(875357637/2000000000 : ℝ)*X 1 0+(2125642843/5000000000 : ℝ)*X 1 1+(450605481/1000000000 : ℝ)*X 1 2+(875357637/2000000000 : ℝ)*X 2 0+(2125642843/5000000000 : ℝ)*X 2 1+(450605481/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-55205259/250000000 : ℝ)*X 0 0+(5264613839/10000000000 : ℝ)*X 0 1+(5394186729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656110977/5000000000 : ℝ)*X 1 0+(-2144381487/10000000000 : ℝ)*X 1 1+(5394186639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312221933/10000000000 : ℝ)*X 2 0+(2697093293/5000000000 : ℝ)*X 2 1+(-536095397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875359577/2000000000 : ℝ)*X 0 0+(1126354267/2500000000 : ℝ)*X 0 1+(4251925979/10000000000 : ℝ)*X 0 2+(875359577/2000000000 : ℝ)*X 1 0+(1126354267/2500000000 : ℝ)*X 1 1+(4251925979/10000000000 : ℝ)*X 1 2+(875359577/2000000000 : ℝ)*X 2 0+(1126354267/2500000000 : ℝ)*X 2 1+(4251925979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1057_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (677662887594883355501739469/115125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1193922733/100000000000000 : ℝ)*(base19) + (1110681887/100000000000000 : ℝ)*(base23) + (5519679/20000000000000 : ℝ)*(lower2) + (81943989/50000000000000 : ℝ)*(upper3) + (79106257/100000000000000 : ℝ)*(upper5) + (1450521794102563/25000000000000 : ℝ)*(major0) + (1450521794102563/25000000000000 : ℝ)*(major1) + (1450521794102563/25000000000000 : ℝ)*(major2) + (7678986164090057/100000000000000 : ℝ)*(sp0) + (3839508294847603/50000000000000 : ℝ)*(sp1) + (1919754168234013/25000000000000 : ℝ)*(sp2) + (3925138434859567/100000000000000 : ℝ)*(sp3) + (31619527883/100000000000000 : ℝ)*(sp4) + (17938132231/100000000000000 : ℝ)*(sp7) + (1962578186495899/50000000000000 : ℝ)*(f.failure) + (383950889180897/5000000000000 : ℝ)*(f.sum) + (48239267283287/13815000000000000000000000000 : ℝ)*base65 + (650282083455184941/76750000000000000000000000000000 : ℝ)*base68 + (264245918618184941/76750000000000000000000000000000 : ℝ)*base70 + (398717297633065059/76750000000000000000000000000000 : ℝ)*base71 + (51412900187/53964843750000000000000000 : ℝ)*base73 + (2224499889625315059/76750000000000000000000000000000 : ℝ)*base75 + (1064088584967565059/76750000000000000000000000000000 : ℝ)*base77 + (525976434104565059/76750000000000000000000000000000 : ℝ)*base79 + (11755052316073/13815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9892197/1250000000000000000000 : ℝ)*base90 + (9892197/1250000000000000000000 : ℝ)*base92 + (9892197/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16350588665444726300201/4605000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229604059/50000000000000 : ℝ)*(base19) + (103335469/20000000000000 : ℝ)*(base23) + (103564247/100000000000000 : ℝ)*(lower1) + (11951879/20000000000000 : ℝ)*(upper2) + (17207103/100000000000000 : ℝ)*(upper5) + (5831281460332051/100000000000000 : ℝ)*(major0) + (5831281460332051/100000000000000 : ℝ)*(major1) + (5831281460332051/100000000000000 : ℝ)*(major2) + (50547737/5000000000000 : ℝ)*(sp0) + (3973225181/100000000000000 : ℝ)*(sp1) + (7717655261893003/100000000000000 : ℝ)*(sp4) + (7717651840414443/100000000000000 : ℝ)*(sp5) + (7717655756170397/100000000000000 : ℝ)*(sp6) + (3944906529462471/100000000000000 : ℝ)*(sp7) + (3944906529462471/100000000000000 : ℝ)*(f.failure) + (3858828136423871/50000000000000 : ℝ)*(f.sum) + (46972276255483/6907500000000000000000000000 : ℝ)*base65 + (3608526408282333357/307000000000000000000000000000000 : ℝ)*base68 + (2821444011419333357/307000000000000000000000000000000 : ℝ)*base70 + (3001776276831333357/307000000000000000000000000000000 : ℝ)*base72 + (12577125951949/13815000000000000000000000000 : ℝ)*base74 + (2059401463107666643/307000000000000000000000000000000 : ℝ)*base75 + (804228395460666643/307000000000000000000000000000000 : ℝ)*base77 + (3783891056222666643/307000000000000000000000000000000 : ℝ)*base79 + (1826792495663/1726875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (21182087/2500000000000000000000 : ℝ)*base89 + (21182087/2500000000000000000000 : ℝ)*base91 + (21182087/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1057_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11237/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1057_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1057_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1057_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1057_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1057_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8249/2048 : ℝ) ≤ p) (hpb : p ≤ (4125/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36954497/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (699/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1057_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
