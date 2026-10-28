-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:50:51.030629+00:00
-- url     : https://prove2.me/submissions/2b757471-7d07-495a-a2cf-1790ed0daabc

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
theorem support_rectangle_w1082_s9_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334058501/625000000 : ℝ)*x 0 + (-1130749683/5000000000 : ℝ)*x 1 + (5264769957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334058501/625000000 : ℝ)^8275 ≤ (43497614191907/100000000000000 : ℝ)^6227 := by
    have hnat : (334058501 : ℕ)^8275*100000000000000^6227 ≤ 43497614191907^6227*625000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334058501 625000000 43497614191907 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130749683/5000000000 : ℝ)^8275 ≤ (433424785463/3125000000000 : ℝ)^6227 := by
    have hnat : (1130749683 : ℕ)^8275*3125000000000^6227 ≤ 433424785463^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130749683 5000000000 433424785463 3125000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264769957/10000000000 : ℝ)^8275 ≤ (21316396333421/50000000000000 : ℝ)^6227 := by
    have hnat : (5264769957 : ℕ)^8275*50000000000000^6227 ≤ 21316396333421^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264769957 10000000000 21316396333421 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334058501/625000000 : ℝ), (-1130749683/5000000000 : ℝ), (5264769957/10000000000 : ℝ)] ![(43497614191907/100000000000000 : ℝ), (433424785463/3125000000000 : ℝ), (21316396333421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334058501/625000000 : ℝ)|^8275 ≤ (43497614191907/100000000000000 : ℝ)^6227
        have hw : |(334058501/625000000 : ℝ)|=(334058501/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1130749683/5000000000 : ℝ)|^8275 ≤ (433424785463/3125000000000 : ℝ)^6227
        have hw : |(-1130749683/5000000000 : ℝ)|=(1130749683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264769957/10000000000 : ℝ)|^8275 ≤ (21316396333421/50000000000000 : ℝ)^6227
        have hw : |(5264769957/10000000000 : ℝ)|=(5264769957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s9_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548979741/2500000000 : ℝ)*x 0 + (2632547393/5000000000 : ℝ)*x 1 + (2696862133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548979741/2500000000 : ℝ)^8275 ≤ (6668839930057/50000000000000 : ℝ)^6227 := by
    have hnat : (548979741 : ℕ)^8275*50000000000000^6227 ≤ 6668839930057^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548979741 2500000000 6668839930057 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632547393/5000000000 : ℝ)^8275 ≤ (21318144097161/50000000000000 : ℝ)^6227 := by
    have hnat : (2632547393 : ℕ)^8275*50000000000000^6227 ≤ 21318144097161^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632547393 5000000000 21318144097161 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696862133/5000000000 : ℝ)^8275 ≤ (44026031928383/100000000000000 : ℝ)^6227 := by
    have hnat : (2696862133 : ℕ)^8275*100000000000000^6227 ≤ 44026031928383^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696862133 5000000000 44026031928383 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548979741/2500000000 : ℝ), (2632547393/5000000000 : ℝ), (2696862133/5000000000 : ℝ)] ![(6668839930057/50000000000000 : ℝ), (21318144097161/50000000000000 : ℝ), (44026031928383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548979741/2500000000 : ℝ)|^8275 ≤ (6668839930057/50000000000000 : ℝ)^6227
        have hw : |(-548979741/2500000000 : ℝ)|=(548979741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632547393/5000000000 : ℝ)|^8275 ≤ (21318144097161/50000000000000 : ℝ)^6227
        have hw : |(2632547393/5000000000 : ℝ)|=(2632547393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696862133/5000000000 : ℝ)|^8275 ≤ (44026031928383/100000000000000 : ℝ)^6227
        have hw : |(2696862133/5000000000 : ℝ)|=(2696862133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s9_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312329919/10000000000 : ℝ)*x 0 + (-106627381/500000000 : ℝ)*x 1 + (5393724281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312329919/10000000000 : ℝ)^8275 ≤ (43145345221733/100000000000000 : ℝ)^6227 := by
    have hnat : (5312329919 : ℕ)^8275*100000000000000^6227 ≤ 43145345221733^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312329919 10000000000 43145345221733 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106627381/500000000 : ℝ)^8275 ≤ (6414311334763/50000000000000 : ℝ)^6227 := by
    have hnat : (106627381 : ℕ)^8275*50000000000000^6227 ≤ 6414311334763^6227*500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106627381 500000000 6414311334763 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393724281/10000000000 : ℝ)^8275 ≤ (2751627005693/6250000000000 : ℝ)^6227 := by
    have hnat : (5393724281 : ℕ)^8275*6250000000000^6227 ≤ 2751627005693^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393724281 10000000000 2751627005693 6250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312329919/10000000000 : ℝ), (-106627381/500000000 : ℝ), (5393724281/10000000000 : ℝ)] ![(43145345221733/100000000000000 : ℝ), (6414311334763/50000000000000 : ℝ), (2751627005693/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312329919/10000000000 : ℝ)|^8275 ≤ (43145345221733/100000000000000 : ℝ)^6227
        have hw : |(5312329919/10000000000 : ℝ)|=(5312329919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106627381/500000000 : ℝ)|^8275 ≤ (6414311334763/50000000000000 : ℝ)^6227
        have hw : |(-106627381/500000000 : ℝ)|=(106627381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393724281/10000000000 : ℝ)|^8275 ≤ (2751627005693/6250000000000 : ℝ)^6227
        have hw : |(5393724281/10000000000 : ℝ)|=(5393724281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s9_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312329771/10000000000 : ℝ)*x 0 + (5393724269/10000000000 : ℝ)*x 1 + (-533136959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312329771/10000000000 : ℝ)^8275 ≤ (674145994131/1562500000000 : ℝ)^6227 := by
    have hnat : (5312329771 : ℕ)^8275*1562500000000^6227 ≤ 674145994131^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312329771 10000000000 674145994131 1562500000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393724269/10000000000 : ℝ)^8275 ≤ (11006507990231/25000000000000 : ℝ)^6227 := by
    have hnat : (5393724269 : ℕ)^8275*25000000000000^6227 ≤ 11006507990231^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393724269 10000000000 11006507990231 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533136959/2500000000 : ℝ)^8275 ≤ (2565724879251/20000000000000 : ℝ)^6227 := by
    have hnat : (533136959 : ℕ)^8275*20000000000000^6227 ≤ 2565724879251^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533136959 2500000000 2565724879251 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312329771/10000000000 : ℝ), (5393724269/10000000000 : ℝ), (-533136959/2500000000 : ℝ)] ![(674145994131/1562500000000 : ℝ), (11006507990231/25000000000000 : ℝ), (2565724879251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312329771/10000000000 : ℝ)|^8275 ≤ (674145994131/1562500000000 : ℝ)^6227
        have hw : |(5312329771/10000000000 : ℝ)|=(5312329771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393724269/10000000000 : ℝ)|^8275 ≤ (11006507990231/25000000000000 : ℝ)^6227
        have hw : |(5393724269/10000000000 : ℝ)|=(5393724269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533136959/2500000000 : ℝ)|^8275 ≤ (2565724879251/20000000000000 : ℝ)^6227
        have hw : |(-533136959/2500000000 : ℝ)|=(533136959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_s9_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373207311/10000000000 : ℝ)*x 0 + (2250755409/5000000000 : ℝ)*x 1 + (33988913/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373207311/10000000000 : ℝ)^8275 ≤ (4164594280841/12500000000000 : ℝ)^6227 := by
    have hnat : (4373207311 : ℕ)^8275*12500000000000^6227 ≤ 4164594280841^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373207311 10000000000 4164594280841 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250755409/5000000000 : ℝ)^8275 ≤ (17310962019697/50000000000000 : ℝ)^6227 := by
    have hnat : (2250755409 : ℕ)^8275*50000000000000^6227 ≤ 17310962019697^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250755409 5000000000 17310962019697 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33988913/80000000 : ℝ)^8275 ≤ (4007665212367/12500000000000 : ℝ)^6227 := by
    have hnat : (33988913 : ℕ)^8275*12500000000000^6227 ≤ 4007665212367^6227*80000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33988913 80000000 4007665212367 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373207311/10000000000 : ℝ), (2250755409/5000000000 : ℝ), (33988913/80000000 : ℝ)] ![(4164594280841/12500000000000 : ℝ), (17310962019697/50000000000000 : ℝ), (4007665212367/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373207311/10000000000 : ℝ)|^8275 ≤ (4164594280841/12500000000000 : ℝ)^6227
        have hw : |(4373207311/10000000000 : ℝ)|=(4373207311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250755409/5000000000 : ℝ)|^8275 ≤ (17310962019697/50000000000000 : ℝ)^6227
        have hw : |(2250755409/5000000000 : ℝ)|=(2250755409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33988913/80000000 : ℝ)|^8275 ≤ (4007665212367/12500000000000 : ℝ)^6227
        have hw : |(33988913/80000000 : ℝ)|=(33988913/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5637/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3503/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5637/50000 : ℝ) ^ (4137/1024 : ℝ) ≤ (57825347274951/390625000000000000 : ℝ) := by
    have hpowers : (5637/50000 : ℝ)^4137 ≤ (57825347274951/390625000000000000 : ℝ)^1024 := by
      have hnat : (5637 : ℕ)^4137*390625000000000000^1024 ≤ 57825347274951^1024*50000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5637 50000 57825347274951 390625000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5637/50000 : ℝ)) (X := (57825347274951/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14013/100000 : ℝ) ^ (4137/1024 : ℝ) ≤ (35641206274304791/100000000000000000000 : ℝ) := by
    have hpowers : (14013/100000 : ℝ)^4137 ≤ (35641206274304791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14013 : ℕ)^4137*100000000000000000000^1024 ≤ 35641206274304791^1024*100000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14013 100000 35641206274304791 100000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14013/100000 : ℝ)) (X := (35641206274304791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (195370325347274951/195312500000000000 : ℝ) ≤ (10000732747381839/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (195370325347274951/195312500000000000 : ℝ)^1024 ≤ (10000732747381839/10000000000000000 : ℝ)^4137 := by
      have hnat : (195370325347274951 : ℕ)^1024*10000000000000000^4137 ≤ 10000732747381839^4137*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195370325347274951 195312500000000000 10000732747381839 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000732747381839/10000000000000000 : ℝ)) (X := (195370325347274951/195312500000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050444495176692247/100000000000000000000 : ℝ) ≤ (50006241885693/50000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (100050444495176692247/100000000000000000000 : ℝ)^1024 ≤ (50006241885693/50000000000000 : ℝ)^4137 := by
      have hnat : (100050444495176692247 : ℕ)^1024*50000000000000^4137 ≤ 50006241885693^4137*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050444495176692247 100000000000000000000 50006241885693 50000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50006241885693/50000000000000 : ℝ)) (X := (100050444495176692247/100000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035641206274304791/50000000000000000000 : ℝ) ≤ (10001764006895361/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50035641206274304791/50000000000000000000 : ℝ)^1024 ≤ (10001764006895361/10000000000000000 : ℝ)^4137 := by
      have hnat : (50035641206274304791 : ℕ)^1024*10000000000000000^4137 ≤ 10001764006895361^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035641206274304791 50000000000000000000 10001764006895361 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001764006895361/10000000000000000 : ℝ)) (X := (50035641206274304791/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(57825347274951/390625000000000000 : ℝ) ≤ ((9126793525107803331/9130000000000000000 : ℝ)+2*(171876585587/91300000000000 : ℝ)*(5637/50000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (9126793525107803331/9130000000000000000 : ℝ)+2*(171876585587/91300000000000 : ℝ)*(5637/50000 : ℝ)=(10000732747381839/10000000000000000 : ℝ) by norm_num, show 1+2*(57825347274951/390625000000000000 : ℝ)=(195370325347274951/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35641206274304791/100000000000000000000 : ℝ)+(57825347274951/390625000000000000 : ℝ) ≤ ((9126793525107803331/9130000000000000000 : ℝ)+(171876585587/91300000000000 : ℝ)*((14013/100000 : ℝ)+(5637/50000 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (9126793525107803331/9130000000000000000 : ℝ)+(171876585587/91300000000000 : ℝ)*((14013/100000 : ℝ)+(5637/50000 : ℝ))=(50006241885693/50000000000000 : ℝ) by norm_num, show 1+(35641206274304791/100000000000000000000 : ℝ)+(57825347274951/390625000000000000 : ℝ)=(100050444495176692247/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35641206274304791/100000000000000000000 : ℝ) ≤ ((9126793525107803331/9130000000000000000 : ℝ)+2*(171876585587/91300000000000 : ℝ)*(14013/100000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (9126793525107803331/9130000000000000000 : ℝ)+2*(171876585587/91300000000000 : ℝ)*(14013/100000 : ℝ)=(10001764006895361/10000000000000000 : ℝ) by norm_num, show 1+2*(35641206274304791/100000000000000000000 : ℝ)=(50035641206274304791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9126793525107803331/9130000000000000000 : ℝ)*(X 1 0+X 2 0)+(171876585587/91300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (9126793525107803331/9130000000000000000 : ℝ)) (alpha := (171876585587/91300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9126793525107803331/9130000000000000000 : ℝ)*(X 0 1+X 2 1)+(171876585587/91300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (9126793525107803331/9130000000000000000 : ℝ)) (alpha := (171876585587/91300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9126793525107803331/9130000000000000000 : ℝ)*(X 0 2+X 1 2)+(171876585587/91300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (9126793525107803331/9130000000000000000 : ℝ)) (alpha := (171876585587/91300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((334058501/625000000 : ℝ)*X 1 0+(-1130749683/5000000000 : ℝ)*X 1 1+(5264769957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-548979741/2500000000 : ℝ)*X 0 0+(2632547393/5000000000 : ℝ)*X 0 1+(2696862133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312329919/10000000000 : ℝ)*X 1 0+(-106627381/500000000 : ℝ)*X 1 1+(5393724281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312329771/10000000000 : ℝ)*X 2 0+(5393724269/10000000000 : ℝ)*X 2 1+(-533136959/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4373207311/10000000000 : ℝ)*X 0 0+(2250755409/5000000000 : ℝ)*X 0 1+(33988913/80000000 : ℝ)*X 0 2+(4373207311/10000000000 : ℝ)*X 1 0+(2250755409/5000000000 : ℝ)*X 1 1+(33988913/80000000 : ℝ)*X 1 2+(4373207311/10000000000 : ℝ)*X 2 0+(2250755409/5000000000 : ℝ)*X 2 1+(33988913/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4575723835910203006525947/1296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17331489/3125000000000 : ℝ)*(base19) + (206017389/50000000000000 : ℝ)*(base23) + (54184051/100000000000000 : ℝ)*(lower1) + (2576821/3125000000000 : ℝ)*(upper2) + (5291917/12500000000000 : ℝ)*(upper3) + (107845693/100000000000000 : ℝ)*(upper5) + (183256861249623/3125000000000 : ℝ)*(major0) + (183256861249623/3125000000000 : ℝ)*(major1) + (183256861249623/3125000000000 : ℝ)*(major2) + (103361199/781250000000 : ℝ)*(sp0) + (3887130528664027/50000000000000 : ℝ)*(sp1) + (3887123636243467/50000000000000 : ℝ)*(sp2) + (1943565161323319/25000000000000 : ℝ)*(sp3) + (1977088972519417/50000000000000 : ℝ)*(sp4) + (1977088972519417/50000000000000 : ℝ)*(f.failure) + (3887130528664027/50000000000000 : ℝ)*(f.sum) + (16751074454119/2282500000000000000000000000 : ℝ)*base66 + (225386969164505787/28531250000000000000000000000000 : ℝ)*base68 + (1486175943841193287/28531250000000000000000000000000 : ℝ)*base70 + (274854125614755787/28531250000000000000000000000000 : ℝ)*base72 + (7300971676567/1141250000000000000000000000 : ℝ)*base74 + (763481857682505787/28531250000000000000000000000000 : ℝ)*base76 + (32755453392068287/28531250000000000000000000000000 : ℝ)*base78 + (487212224614505787/28531250000000000000000000000000 : ℝ)*base80 + (95284778501489/2282500000000000000000000000 : ℝ)*base82 + (5797433/625000000000000000000 : ℝ)*base89 + (5797433/625000000000000000000 : ℝ)*base91 + (5797433/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1082_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1082_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1082_box_0 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2067010521/10000000000 : ℝ)*x 0 + (168035851/312500000 : ℝ)*x 1 + (2688573571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067010521/10000000000 : ℝ)^8275 ≤ (1538422205883/12500000000000 : ℝ)^6227 := by
    have hnat : (2067010521 : ℕ)^8275*12500000000000^6227 ≤ 1538422205883^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067010521 10000000000 1538422205883 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168035851/312500000 : ℝ)^8275 ≤ (1096157791411/2500000000000 : ℝ)^6227 := by
    have hnat : (168035851 : ℕ)^8275*2500000000000^6227 ≤ 1096157791411^6227*312500000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168035851 312500000 1096157791411 2500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688573571/5000000000 : ℝ)^8275 ≤ (43846310681197/100000000000000 : ℝ)^6227 := by
    have hnat : (2688573571 : ℕ)^8275*100000000000000^6227 ≤ 43846310681197^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688573571 5000000000 43846310681197 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2067010521/10000000000 : ℝ), (168035851/312500000 : ℝ), (2688573571/5000000000 : ℝ)] ![(1538422205883/12500000000000 : ℝ), (1096157791411/2500000000000 : ℝ), (43846310681197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2067010521/10000000000 : ℝ)|^8275 ≤ (1538422205883/12500000000000 : ℝ)^6227
        have hw : |(-2067010521/10000000000 : ℝ)|=(2067010521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168035851/312500000 : ℝ)|^8275 ≤ (1096157791411/2500000000000 : ℝ)^6227
        have hw : |(168035851/312500000 : ℝ)|=(168035851/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688573571/5000000000 : ℝ)|^8275 ≤ (43846310681197/100000000000000 : ℝ)^6227
        have hw : |(2688573571/5000000000 : ℝ)|=(2688573571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_1 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (105907621/200000000 : ℝ)*x 0 + (-54443583/250000000 : ℝ)*x 1 + (5377147129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105907621/200000000 : ℝ)^8275 ≤ (21481256930789/50000000000000 : ℝ)^6227 := by
    have hnat : (105907621 : ℕ)^8275*50000000000000^6227 ≤ 21481256930789^6227*200000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105907621 200000000 21481256930789 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54443583/250000000 : ℝ)^8275 ≤ (3297793896309/25000000000000 : ℝ)^6227 := by
    have hnat : (54443583 : ℕ)^8275*25000000000000^6227 ≤ 3297793896309^6227*250000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54443583 250000000 3297793896309 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377147129/10000000000 : ℝ)^8275 ≤ (43846310540329/100000000000000 : ℝ)^6227 := by
    have hnat : (5377147129 : ℕ)^8275*100000000000000^6227 ≤ 43846310540329^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377147129 10000000000 43846310540329 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105907621/200000000 : ℝ), (-54443583/250000000 : ℝ), (5377147129/10000000000 : ℝ)] ![(21481256930789/50000000000000 : ℝ), (3297793896309/25000000000000 : ℝ), (43846310540329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105907621/200000000 : ℝ)|^8275 ≤ (21481256930789/50000000000000 : ℝ)^6227
        have hw : |(105907621/200000000 : ℝ)|=(105907621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54443583/250000000 : ℝ)|^8275 ≤ (3297793896309/25000000000000 : ℝ)^6227
        have hw : |(-54443583/250000000 : ℝ)|=(54443583/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377147129/10000000000 : ℝ)|^8275 ≤ (43846310540329/100000000000000 : ℝ)^6227
        have hw : |(5377147129/10000000000 : ℝ)|=(5377147129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_2 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647690401/5000000000 : ℝ)*x 0 + (5377147363/10000000000 : ℝ)*x 1 + (-2177743337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647690401/5000000000 : ℝ)^8275 ≤ (42962511187751/100000000000000 : ℝ)^6227 := by
    have hnat : (2647690401 : ℕ)^8275*100000000000000^6227 ≤ 42962511187751^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647690401 5000000000 42962511187751 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377147363/10000000000 : ℝ)^8275 ≤ (43846313075961/100000000000000 : ℝ)^6227 := by
    have hnat : (5377147363 : ℕ)^8275*100000000000000^6227 ≤ 43846313075961^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377147363 10000000000 43846313075961 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177743337/10000000000 : ℝ)^8275 ≤ (3297793930519/25000000000000 : ℝ)^6227 := by
    have hnat : (2177743337 : ℕ)^8275*25000000000000^6227 ≤ 3297793930519^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177743337 10000000000 3297793930519 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647690401/5000000000 : ℝ), (5377147363/10000000000 : ℝ), (-2177743337/10000000000 : ℝ)] ![(42962511187751/100000000000000 : ℝ), (43846313075961/100000000000000 : ℝ), (3297793930519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647690401/5000000000 : ℝ)|^8275 ≤ (42962511187751/100000000000000 : ℝ)^6227
        have hw : |(2647690401/5000000000 : ℝ)|=(2647690401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377147363/10000000000 : ℝ)|^8275 ≤ (43846313075961/100000000000000 : ℝ)^6227
        have hw : |(5377147363/10000000000 : ℝ)|=(5377147363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177743337/10000000000 : ℝ)|^8275 ≤ (3297793930519/25000000000000 : ℝ)^6227
        have hw : |(-2177743337/10000000000 : ℝ)|=(2177743337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_3 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4481398161/10000000000 : ℝ)*x 0 + (864249537/2000000000 : ℝ)*x 1 + (4321247573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4481398161/10000000000 : ℝ)^8275 ≤ (34416509133231/100000000000000 : ℝ)^6227 := by
    have hnat : (4481398161 : ℕ)^8275*100000000000000^6227 ≤ 34416509133231^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481398161 10000000000 34416509133231 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864249537/2000000000 : ℝ)^8275 ≤ (16395872994817/50000000000000 : ℝ)^6227 := by
    have hnat : (864249537 : ℕ)^8275*50000000000000^6227 ≤ 16395872994817^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864249537 2000000000 16395872994817 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4321247573/10000000000 : ℝ)^8275 ≤ (8197936215049/25000000000000 : ℝ)^6227 := by
    have hnat : (4321247573 : ℕ)^8275*25000000000000^6227 ≤ 8197936215049^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321247573 10000000000 8197936215049 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4481398161/10000000000 : ℝ), (864249537/2000000000 : ℝ), (4321247573/10000000000 : ℝ)] ![(34416509133231/100000000000000 : ℝ), (16395872994817/50000000000000 : ℝ), (8197936215049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4481398161/10000000000 : ℝ)|^8275 ≤ (34416509133231/100000000000000 : ℝ)^6227
        have hw : |(4481398161/10000000000 : ℝ)|=(4481398161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(864249537/2000000000 : ℝ)|^8275 ≤ (16395872994817/50000000000000 : ℝ)^6227
        have hw : |(864249537/2000000000 : ℝ)|=(864249537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4321247573/10000000000 : ℝ)|^8275 ≤ (8197936215049/25000000000000 : ℝ)^6227
        have hw : |(4321247573/10000000000 : ℝ)|=(4321247573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_4 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-465241977/2000000000 : ℝ)*x 0 + (1320081599/2500000000 : ℝ)*x 1 + (5280326157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465241977/2000000000 : ℝ)^8275 ≤ (14399448278271/100000000000000 : ℝ)^6227 := by
    have hnat : (465241977 : ℕ)^8275*100000000000000^6227 ≤ 14399448278271^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465241977 2000000000 14399448278271 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320081599/2500000000 : ℝ)^8275 ≤ (5350034642201/12500000000000 : ℝ)^6227 := by
    have hnat : (1320081599 : ℕ)^8275*12500000000000^6227 ≤ 5350034642201^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320081599 2500000000 5350034642201 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280326157/10000000000 : ℝ)^8275 ≤ (42800274563227/100000000000000 : ℝ)^6227 := by
    have hnat : (5280326157 : ℕ)^8275*100000000000000^6227 ≤ 42800274563227^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280326157 10000000000 42800274563227 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-465241977/2000000000 : ℝ), (1320081599/2500000000 : ℝ), (5280326157/10000000000 : ℝ)] ![(14399448278271/100000000000000 : ℝ), (5350034642201/12500000000000 : ℝ), (42800274563227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-465241977/2000000000 : ℝ)|^8275 ≤ (14399448278271/100000000000000 : ℝ)^6227
        have hw : |(-465241977/2000000000 : ℝ)|=(465241977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320081599/2500000000 : ℝ)|^8275 ≤ (5350034642201/12500000000000 : ℝ)^6227
        have hw : |(1320081599/2500000000 : ℝ)|=(1320081599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280326157/10000000000 : ℝ)|^8275 ≤ (42800274563227/100000000000000 : ℝ)^6227
        have hw : |(5280326157/10000000000 : ℝ)|=(5280326157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_5 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681938821/5000000000 : ℝ)*x 0 + (-1107823143/5000000000 : ℝ)*x 1 + (1320081581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681938821/5000000000 : ℝ)^8275 ≤ (21851290169947/50000000000000 : ℝ)^6227 := by
    have hnat : (2681938821 : ℕ)^8275*50000000000000^6227 ≤ 21851290169947^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681938821 5000000000 21851290169947 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107823143/5000000000 : ℝ)^8275 ≤ (13497143283433/100000000000000 : ℝ)^6227 := by
    have hnat : (1107823143 : ℕ)^8275*100000000000000^6227 ≤ 13497143283433^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107823143 5000000000 13497143283433 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320081581/2500000000 : ℝ)^8275 ≤ (21400138181031/50000000000000 : ℝ)^6227 := by
    have hnat : (1320081581 : ℕ)^8275*50000000000000^6227 ≤ 21400138181031^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320081581 2500000000 21400138181031 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681938821/5000000000 : ℝ), (-1107823143/5000000000 : ℝ), (1320081581/2500000000 : ℝ)] ![(21851290169947/50000000000000 : ℝ), (13497143283433/100000000000000 : ℝ), (21400138181031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681938821/5000000000 : ℝ)|^8275 ≤ (21851290169947/50000000000000 : ℝ)^6227
        have hw : |(2681938821/5000000000 : ℝ)|=(2681938821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1107823143/5000000000 : ℝ)|^8275 ≤ (13497143283433/100000000000000 : ℝ)^6227
        have hw : |(-1107823143/5000000000 : ℝ)|=(1107823143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320081581/2500000000 : ℝ)|^8275 ≤ (21400138181031/50000000000000 : ℝ)^6227
        have hw : |(1320081581/2500000000 : ℝ)|=(1320081581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_6 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363877713/10000000000 : ℝ)*x 0 + (264016333/500000000 : ℝ)*x 1 + (-138477859/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363877713/10000000000 : ℝ)^8275 ≤ (10925645277157/25000000000000 : ℝ)^6227 := by
    have hnat : (5363877713 : ℕ)^8275*25000000000000^6227 ≤ 10925645277157^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363877713 10000000000 10925645277157 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264016333/500000000 : ℝ)^8275 ≤ (10700069995319/25000000000000 : ℝ)^6227 := by
    have hnat : (264016333 : ℕ)^8275*25000000000000^6227 ≤ 10700069995319^6227*500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264016333 500000000 10700069995319 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138477859/625000000 : ℝ)^8275 ≤ (3374284723951/25000000000000 : ℝ)^6227 := by
    have hnat : (138477859 : ℕ)^8275*25000000000000^6227 ≤ 3374284723951^6227*625000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138477859 625000000 3374284723951 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363877713/10000000000 : ℝ), (264016333/500000000 : ℝ), (-138477859/625000000 : ℝ)] ![(10925645277157/25000000000000 : ℝ), (10700069995319/25000000000000 : ℝ), (3374284723951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363877713/10000000000 : ℝ)|^8275 ≤ (10925645277157/25000000000000 : ℝ)^6227
        have hw : |(5363877713/10000000000 : ℝ)|=(5363877713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264016333/500000000 : ℝ)|^8275 ≤ (10700069995319/25000000000000 : ℝ)^6227
        have hw : |(264016333/500000000 : ℝ)|=(264016333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138477859/625000000 : ℝ)|^8275 ≤ (3374284723951/25000000000000 : ℝ)^6227
        have hw : |(-138477859/625000000 : ℝ)|=(138477859/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_7 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1066165269/2500000000 : ℝ)*x 0 + (4429594937/10000000000 : ℝ)*x 1 + (2214797381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066165269/2500000000 : ℝ)^8275 ≤ (32222343703359/100000000000000 : ℝ)^6227 := by
    have hnat : (1066165269 : ℕ)^8275*100000000000000^6227 ≤ 32222343703359^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066165269 2500000000 32222343703359 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4429594937/10000000000 : ℝ)^8275 ≤ (16944414516177/50000000000000 : ℝ)^6227 := by
    have hnat : (4429594937 : ℕ)^8275*50000000000000^6227 ≤ 16944414516177^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429594937 10000000000 16944414516177 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214797381/5000000000 : ℝ)^8275 ≤ (16944413626587/50000000000000 : ℝ)^6227 := by
    have hnat : (2214797381 : ℕ)^8275*50000000000000^6227 ≤ 16944413626587^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214797381 5000000000 16944413626587 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066165269/2500000000 : ℝ), (4429594937/10000000000 : ℝ), (2214797381/5000000000 : ℝ)] ![(32222343703359/100000000000000 : ℝ), (16944414516177/50000000000000 : ℝ), (16944413626587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066165269/2500000000 : ℝ)|^8275 ≤ (32222343703359/100000000000000 : ℝ)^6227
        have hw : |(1066165269/2500000000 : ℝ)|=(1066165269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4429594937/10000000000 : ℝ)|^8275 ≤ (16944414516177/50000000000000 : ℝ)^6227
        have hw : |(4429594937/10000000000 : ℝ)|=(4429594937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2214797381/5000000000 : ℝ)|^8275 ≤ (16944413626587/50000000000000 : ℝ)^6227
        have hw : |(2214797381/5000000000 : ℝ)|=(2214797381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_8 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2272079601/10000000000 : ℝ)*x 0 + (1303649079/2500000000 : ℝ)*x 1 + (5386749339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272079601/10000000000 : ℝ)^8275 ≤ (3488972019433/25000000000000 : ℝ)^6227 := by
    have hnat : (2272079601 : ℕ)^8275*25000000000000^6227 ≤ 3488972019433^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272079601 10000000000 3488972019433 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303649079/2500000000 : ℝ)^8275 ≤ (42093720971551/100000000000000 : ℝ)^6227 := by
    have hnat : (1303649079 : ℕ)^8275*100000000000000^6227 ≤ 42093720971551^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303649079 2500000000 42093720971551 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386749339/10000000000 : ℝ)^8275 ≤ (10987597734093/25000000000000 : ℝ)^6227 := by
    have hnat : (5386749339 : ℕ)^8275*25000000000000^6227 ≤ 10987597734093^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386749339 10000000000 10987597734093 25000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2272079601/10000000000 : ℝ), (1303649079/2500000000 : ℝ), (5386749339/10000000000 : ℝ)] ![(3488972019433/25000000000000 : ℝ), (42093720971551/100000000000000 : ℝ), (10987597734093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2272079601/10000000000 : ℝ)|^8275 ≤ (3488972019433/25000000000000 : ℝ)^6227
        have hw : |(-2272079601/10000000000 : ℝ)|=(2272079601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303649079/2500000000 : ℝ)|^8275 ≤ (42093720971551/100000000000000 : ℝ)^6227
        have hw : |(1303649079/2500000000 : ℝ)|=(1303649079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386749339/10000000000 : ℝ)|^8275 ≤ (10987597734093/25000000000000 : ℝ)^6227
        have hw : |(5386749339/10000000000 : ℝ)|=(5386749339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_9 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288584147/10000000000 : ℝ)*x 0 + (-2173913383/10000000000 : ℝ)*x 1 + (5386749827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288584147/10000000000 : ℝ)^8275 ≤ (42889248116121/100000000000000 : ℝ)^6227 := by
    have hnat : (5288584147 : ℕ)^8275*100000000000000^6227 ≤ 42889248116121^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288584147 10000000000 42889248116121 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173913383/10000000000 : ℝ)^8275 ≤ (13160355636643/100000000000000 : ℝ)^6227 := by
    have hnat : (2173913383 : ℕ)^8275*100000000000000^6227 ≤ 13160355636643^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173913383 10000000000 13160355636643 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386749827/10000000000 : ℝ)^8275 ≤ (2197519811373/5000000000000 : ℝ)^6227 := by
    have hnat : (5386749827 : ℕ)^8275*5000000000000^6227 ≤ 2197519811373^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386749827 10000000000 2197519811373 5000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288584147/10000000000 : ℝ), (-2173913383/10000000000 : ℝ), (5386749827/10000000000 : ℝ)] ![(42889248116121/100000000000000 : ℝ), (13160355636643/100000000000000 : ℝ), (2197519811373/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288584147/10000000000 : ℝ)|^8275 ≤ (42889248116121/100000000000000 : ℝ)^6227
        have hw : |(5288584147/10000000000 : ℝ)|=(5288584147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173913383/10000000000 : ℝ)|^8275 ≤ (13160355636643/100000000000000 : ℝ)^6227
        have hw : |(-2173913383/10000000000 : ℝ)|=(2173913383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386749827/10000000000 : ℝ)|^8275 ≤ (2197519811373/5000000000000 : ℝ)^6227
        have hw : |(5386749827/10000000000 : ℝ)|=(5386749827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_10 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288584139/10000000000 : ℝ)*x 0 + (538674927/1000000000 : ℝ)*x 1 + (-1086957073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288584139/10000000000 : ℝ)^8275 ≤ (8577849605981/20000000000000 : ℝ)^6227 := by
    have hnat : (5288584139 : ℕ)^8275*20000000000000^6227 ≤ 8577849605981^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288584139 10000000000 8577849605981 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538674927/1000000000 : ℝ)^8275 ≤ (43950390188247/100000000000000 : ℝ)^6227 := by
    have hnat : (538674927 : ℕ)^8275*100000000000000^6227 ≤ 43950390188247^6227*1000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538674927 1000000000 43950390188247 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086957073/5000000000 : ℝ)^8275 ≤ (411261305463/3125000000000 : ℝ)^6227 := by
    have hnat : (1086957073 : ℕ)^8275*3125000000000^6227 ≤ 411261305463^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086957073 5000000000 411261305463 3125000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288584139/10000000000 : ℝ), (538674927/1000000000 : ℝ), (-1086957073/5000000000 : ℝ)] ![(8577849605981/20000000000000 : ℝ), (43950390188247/100000000000000 : ℝ), (411261305463/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288584139/10000000000 : ℝ)|^8275 ≤ (8577849605981/20000000000000 : ℝ)^6227
        have hw : |(5288584139/10000000000 : ℝ)|=(5288584139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538674927/1000000000 : ℝ)|^8275 ≤ (43950390188247/100000000000000 : ℝ)^6227
        have hw : |(538674927/1000000000 : ℝ)|=(538674927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086957073/5000000000 : ℝ)|^8275 ≤ (411261305463/3125000000000 : ℝ)^6227
        have hw : |(-1086957073/5000000000 : ℝ)|=(1086957073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_11 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2251310283/5000000000 : ℝ)*x 0 + (4310495859/10000000000 : ℝ)*x 1 + (2155247977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251310283/5000000000 : ℝ)^8275 ≤ (34633266937057/100000000000000 : ℝ)^6227 := by
    have hnat : (2251310283 : ℕ)^8275*100000000000000^6227 ≤ 34633266937057^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251310283 5000000000 34633266937057 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4310495859/10000000000 : ℝ)^8275 ≤ (32683366047763/100000000000000 : ℝ)^6227 := by
    have hnat : (4310495859 : ℕ)^8275*100000000000000^6227 ≤ 32683366047763^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310495859 10000000000 32683366047763 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155247977/5000000000 : ℝ)^8275 ≤ (4085420875623/12500000000000 : ℝ)^6227 := by
    have hnat : (2155247977 : ℕ)^8275*12500000000000^6227 ≤ 4085420875623^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155247977 5000000000 4085420875623 12500000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251310283/5000000000 : ℝ), (4310495859/10000000000 : ℝ), (2155247977/5000000000 : ℝ)] ![(34633266937057/100000000000000 : ℝ), (32683366047763/100000000000000 : ℝ), (4085420875623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251310283/5000000000 : ℝ)|^8275 ≤ (34633266937057/100000000000000 : ℝ)^6227
        have hw : |(2251310283/5000000000 : ℝ)|=(2251310283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4310495859/10000000000 : ℝ)|^8275 ≤ (32683366047763/100000000000000 : ℝ)^6227
        have hw : |(4310495859/10000000000 : ℝ)|=(4310495859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2155247977/5000000000 : ℝ)|^8275 ≤ (4085420875623/12500000000000 : ℝ)^6227
        have hw : |(2155247977/5000000000 : ℝ)|=(2155247977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_12 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121498809/10000000000 : ℝ)*x 0 + (5441553937/10000000000 : ℝ)*x 1 + (1054463511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121498809/10000000000 : ℝ)^8275 ≤ (12740372536319/100000000000000 : ℝ)^6227 := by
    have hnat : (2121498809 : ℕ)^8275*100000000000000^6227 ≤ 12740372536319^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121498809 10000000000 12740372536319 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441553937/10000000000 : ℝ)^8275 ≤ (44545595781611/100000000000000 : ℝ)^6227 := by
    have hnat : (5441553937 : ℕ)^8275*100000000000000^6227 ≤ 44545595781611^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441553937 10000000000 44545595781611 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054463511/2000000000 : ℝ)^8275 ≤ (21357015838181/50000000000000 : ℝ)^6227 := by
    have hnat : (1054463511 : ℕ)^8275*50000000000000^6227 ≤ 21357015838181^6227*2000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054463511 2000000000 21357015838181 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121498809/10000000000 : ℝ), (5441553937/10000000000 : ℝ), (1054463511/2000000000 : ℝ)] ![(12740372536319/100000000000000 : ℝ), (44545595781611/100000000000000 : ℝ), (21357015838181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121498809/10000000000 : ℝ)|^8275 ≤ (12740372536319/100000000000000 : ℝ)^6227
        have hw : |(-2121498809/10000000000 : ℝ)|=(2121498809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441553937/10000000000 : ℝ)|^8275 ≤ (44545595781611/100000000000000 : ℝ)^6227
        have hw : |(5441553937/10000000000 : ℝ)|=(5441553937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054463511/2000000000 : ℝ)|^8275 ≤ (21357015838181/50000000000000 : ℝ)^6227
        have hw : |(1054463511/2000000000 : ℝ)|=(1054463511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_13 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684770831/5000000000 : ℝ)*x 0 + (-554680611/2500000000 : ℝ)*x 1 + (2636158797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684770831/5000000000 : ℝ)^8275 ≤ (21881958316241/50000000000000 : ℝ)^6227 := by
    have hnat : (2684770831 : ℕ)^8275*50000000000000^6227 ≤ 21881958316241^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684770831 5000000000 21881958316241 50000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554680611/2500000000 : ℝ)^8275 ≤ (13522051252447/100000000000000 : ℝ)^6227 := by
    have hnat : (554680611 : ℕ)^8275*100000000000000^6227 ≤ 13522051252447^6227*2500000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554680611 2500000000 13522051252447 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636158797/5000000000 : ℝ)^8275 ≤ (533925401203/1250000000000 : ℝ)^6227 := by
    have hnat : (2636158797 : ℕ)^8275*1250000000000^6227 ≤ 533925401203^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636158797 5000000000 533925401203 1250000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684770831/5000000000 : ℝ), (-554680611/2500000000 : ℝ), (2636158797/5000000000 : ℝ)] ![(21881958316241/50000000000000 : ℝ), (13522051252447/100000000000000 : ℝ), (533925401203/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684770831/5000000000 : ℝ)|^8275 ≤ (21881958316241/50000000000000 : ℝ)^6227
        have hw : |(2684770831/5000000000 : ℝ)|=(2684770831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-554680611/2500000000 : ℝ)|^8275 ≤ (13522051252447/100000000000000 : ℝ)^6227
        have hw : |(-554680611/2500000000 : ℝ)|=(554680611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636158797/5000000000 : ℝ)|^8275 ≤ (533925401203/1250000000000 : ℝ)^6227
        have hw : |(2636158797/5000000000 : ℝ)|=(2636158797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_14 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369541531/10000000000 : ℝ)*x 0 + (329519803/625000000 : ℝ)*x 1 + (-2218723611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369541531/10000000000 : ℝ)^8275 ≤ (43763915213623/100000000000000 : ℝ)^6227 := by
    have hnat : (5369541531 : ℕ)^8275*100000000000000^6227 ≤ 43763915213623^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369541531 10000000000 43763915213623 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329519803/625000000 : ℝ)^8275 ≤ (8542804812947/20000000000000 : ℝ)^6227 := by
    have hnat : (329519803 : ℕ)^8275*20000000000000^6227 ≤ 8542804812947^6227*625000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329519803 625000000 8542804812947 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218723611/10000000000 : ℝ)^8275 ≤ (13522060703923/100000000000000 : ℝ)^6227 := by
    have hnat : (2218723611 : ℕ)^8275*100000000000000^6227 ≤ 13522060703923^6227*10000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218723611 10000000000 13522060703923 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369541531/10000000000 : ℝ), (329519803/625000000 : ℝ), (-2218723611/10000000000 : ℝ)] ![(43763915213623/100000000000000 : ℝ), (8542804812947/20000000000000 : ℝ), (13522060703923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369541531/10000000000 : ℝ)|^8275 ≤ (43763915213623/100000000000000 : ℝ)^6227
        have hw : |(5369541531/10000000000 : ℝ)|=(5369541531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329519803/625000000 : ℝ)|^8275 ≤ (8542804812947/20000000000000 : ℝ)^6227
        have hw : |(329519803/625000000 : ℝ)|=(329519803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2218723611/10000000000 : ℝ)|^8275 ≤ (13522060703923/100000000000000 : ℝ)^6227
        have hw : |(-2218723611/10000000000 : ℝ)|=(2218723611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1082_box_15 (p : ℝ) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2123250403/5000000000 : ℝ)*x 0 + (2219276393/5000000000 : ℝ)*x 1 + (2219276713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123250403/5000000000 : ℝ)^8275 ≤ (6408026126647/20000000000000 : ℝ)^6227 := by
    have hnat : (2123250403 : ℕ)^8275*20000000000000^6227 ≤ 6408026126647^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123250403 5000000000 6408026126647 20000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219276393/5000000000 : ℝ)^8275 ≤ (33979931420043/100000000000000 : ℝ)^6227 := by
    have hnat : (2219276393 : ℕ)^8275*100000000000000^6227 ≤ 33979931420043^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219276393 5000000000 33979931420043 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2219276713/5000000000 : ℝ)^8275 ≤ (33979937931081/100000000000000 : ℝ)^6227 := by
    have hnat : (2219276713 : ℕ)^8275*100000000000000^6227 ≤ 33979937931081^6227*5000000000^8275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219276713 5000000000 33979937931081 100000000000000 8275 6227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8275/2048 : ℝ)) 8275 6227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123250403/5000000000 : ℝ), (2219276393/5000000000 : ℝ), (2219276713/5000000000 : ℝ)] ![(6408026126647/20000000000000 : ℝ), (33979931420043/100000000000000 : ℝ), (33979937931081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123250403/5000000000 : ℝ)|^8275 ≤ (6408026126647/20000000000000 : ℝ)^6227
        have hw : |(2123250403/5000000000 : ℝ)|=(2123250403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2219276393/5000000000 : ℝ)|^8275 ≤ (33979931420043/100000000000000 : ℝ)^6227
        have hw : |(2219276393/5000000000 : ℝ)|=(2219276393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2219276713/5000000000 : ℝ)|^8275 ≤ (33979937931081/100000000000000 : ℝ)^6227
        have hw : |(2219276713/5000000000 : ℝ)|=(2219276713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1082_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59253/100000 : ℝ) ∧ (79623/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82989/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5637/50000 : ℝ) ^ (4137/1024 : ℝ) ≤ (57825347274951/390625000000000000 : ℝ) := by
    have hpowers : (5637/50000 : ℝ)^4137 ≤ (57825347274951/390625000000000000 : ℝ)^1024 := by
      have hnat : (5637 : ℕ)^4137*390625000000000000^1024 ≤ 57825347274951^1024*50000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5637 50000 57825347274951 390625000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5637/50000 : ℝ)) (X := (57825347274951/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3503/25000 : ℝ) ^ (4137/1024 : ℝ) ≤ (3563093179723059/10000000000000000000 : ℝ) := by
    have hpowers : (3503/25000 : ℝ)^4137 ≤ (3563093179723059/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3503 : ℕ)^4137*10000000000000000000^1024 ≤ 3563093179723059^1024*25000^4137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3503 25000 3563093179723059 10000000000000000000 4137 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3503/25000 : ℝ)) (X := (3563093179723059/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (195370325347274951/195312500000000000 : ℝ) ≤ (10000732747381839/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (195370325347274951/195312500000000000 : ℝ)^1024 ≤ (10000732747381839/10000000000000000 : ℝ)^4137 := by
      have hnat : (195370325347274951 : ℕ)^1024*10000000000000000^4137 ≤ 10000732747381839^4137*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195370325347274951 195312500000000000 10000732747381839 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000732747381839/10000000000000000 : ℝ)) (X := (195370325347274951/195312500000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025217110349809023/50000000000000000000 : ℝ) ≤ (10001248122918801/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (50025217110349809023/50000000000000000000 : ℝ)^1024 ≤ (10001248122918801/10000000000000000 : ℝ)^4137 := by
      have hnat : (50025217110349809023 : ℕ)^1024*10000000000000000^4137 ≤ 10001248122918801^4137*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025217110349809023 50000000000000000000 10001248122918801 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001248122918801/10000000000000000 : ℝ)) (X := (50025217110349809023/50000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003563093179723059/5000000000000000000 : ℝ) ≤ (10001763498455763/10000000000000000 : ℝ) ^ (4137/1024 : ℝ) := by
    have hpowers : (5003563093179723059/5000000000000000000 : ℝ)^1024 ≤ (10001763498455763/10000000000000000 : ℝ)^4137 := by
      have hnat : (5003563093179723059 : ℕ)^1024*10000000000000000^4137 ≤ 10001763498455763^4137*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003563093179723059 5000000000000000000 10001763498455763 10000000000000000 1024 4137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001763498455763/10000000000000000 : ℝ)) (X := (5003563093179723059/5000000000000000000 : ℝ)) (by norm_num) 4137 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(57825347274951/390625000000000000 : ℝ) ≤ ((13685192787362028003/13690000000000000000 : ℝ)+2*(257687768481/136900000000000 : ℝ)*(5637/50000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (13685192787362028003/13690000000000000000 : ℝ)+2*(257687768481/136900000000000 : ℝ)*(5637/50000 : ℝ)=(10000732747381839/10000000000000000 : ℝ) by norm_num, show 1+2*(57825347274951/390625000000000000 : ℝ)=(195370325347274951/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3563093179723059/10000000000000000000 : ℝ)+(57825347274951/390625000000000000 : ℝ) ≤ ((13685192787362028003/13690000000000000000 : ℝ)+(257687768481/136900000000000 : ℝ)*((3503/25000 : ℝ)+(5637/50000 : ℝ)))^(4137/1024 : ℝ) := by
    rw [show (13685192787362028003/13690000000000000000 : ℝ)+(257687768481/136900000000000 : ℝ)*((3503/25000 : ℝ)+(5637/50000 : ℝ))=(10001248122918801/10000000000000000 : ℝ) by norm_num, show 1+(3563093179723059/10000000000000000000 : ℝ)+(57825347274951/390625000000000000 : ℝ)=(50025217110349809023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3563093179723059/10000000000000000000 : ℝ) ≤ ((13685192787362028003/13690000000000000000 : ℝ)+2*(257687768481/136900000000000 : ℝ)*(3503/25000 : ℝ))^(4137/1024 : ℝ) := by
    rw [show (13685192787362028003/13690000000000000000 : ℝ)+2*(257687768481/136900000000000 : ℝ)*(3503/25000 : ℝ)=(10001763498455763/10000000000000000 : ℝ) by norm_num, show 1+2*(3563093179723059/10000000000000000000 : ℝ)=(5003563093179723059/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13685192787362028003/13690000000000000000 : ℝ)*(X 1 0+X 2 0)+(257687768481/136900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (13685192787362028003/13690000000000000000 : ℝ)) (alpha := (257687768481/136900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13685192787362028003/13690000000000000000 : ℝ)*(X 0 1+X 2 1)+(257687768481/136900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (13685192787362028003/13690000000000000000 : ℝ)) (alpha := (257687768481/136900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13685192787362028003/13690000000000000000 : ℝ)*(X 0 2+X 1 2)+(257687768481/136900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4137/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (3503/25000 : ℝ)) (c := (13685192787362028003/13690000000000000000 : ℝ)) (alpha := (257687768481/136900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2067010521/10000000000 : ℝ)*X 0 0+(168035851/312500000 : ℝ)*X 0 1+(2688573571/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((105907621/200000000 : ℝ)*X 1 0+(-54443583/250000000 : ℝ)*X 1 1+(5377147129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647690401/5000000000 : ℝ)*X 2 0+(5377147363/10000000000 : ℝ)*X 2 1+(-2177743337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4481398161/10000000000 : ℝ)*X 0 0+(864249537/2000000000 : ℝ)*X 0 1+(4321247573/10000000000 : ℝ)*X 0 2+(4481398161/10000000000 : ℝ)*X 1 0+(864249537/2000000000 : ℝ)*X 1 1+(4321247573/10000000000 : ℝ)*X 1 2+(4481398161/10000000000 : ℝ)*X 2 0+(864249537/2000000000 : ℝ)*X 2 1+(4321247573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-465241977/2000000000 : ℝ)*X 0 0+(1320081599/2500000000 : ℝ)*X 0 1+(5280326157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681938821/5000000000 : ℝ)*X 1 0+(-1107823143/5000000000 : ℝ)*X 1 1+(1320081581/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363877713/10000000000 : ℝ)*X 2 0+(264016333/500000000 : ℝ)*X 2 1+(-138477859/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1066165269/2500000000 : ℝ)*X 0 0+(4429594937/10000000000 : ℝ)*X 0 1+(2214797381/5000000000 : ℝ)*X 0 2+(1066165269/2500000000 : ℝ)*X 1 0+(4429594937/10000000000 : ℝ)*X 1 1+(2214797381/5000000000 : ℝ)*X 1 2+(1066165269/2500000000 : ℝ)*X 2 0+(4429594937/10000000000 : ℝ)*X 2 1+(2214797381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2272079601/10000000000 : ℝ)*X 0 0+(1303649079/2500000000 : ℝ)*X 0 1+(5386749339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288584147/10000000000 : ℝ)*X 1 0+(-2173913383/10000000000 : ℝ)*X 1 1+(5386749827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288584139/10000000000 : ℝ)*X 2 0+(538674927/1000000000 : ℝ)*X 2 1+(-1086957073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251310283/5000000000 : ℝ)*X 0 0+(4310495859/10000000000 : ℝ)*X 0 1+(2155247977/5000000000 : ℝ)*X 0 2+(2251310283/5000000000 : ℝ)*X 1 0+(4310495859/10000000000 : ℝ)*X 1 1+(2155247977/5000000000 : ℝ)*X 1 2+(2251310283/5000000000 : ℝ)*X 2 0+(4310495859/10000000000 : ℝ)*X 2 1+(2155247977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2121498809/10000000000 : ℝ)*X 0 0+(5441553937/10000000000 : ℝ)*X 0 1+(1054463511/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684770831/5000000000 : ℝ)*X 1 0+(-554680611/2500000000 : ℝ)*X 1 1+(2636158797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369541531/10000000000 : ℝ)*X 2 0+(329519803/625000000 : ℝ)*X 2 1+(-2218723611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2123250403/5000000000 : ℝ)*X 0 0+(2219276393/5000000000 : ℝ)*X 0 1+(2219276713/5000000000 : ℝ)*X 0 2+(2123250403/5000000000 : ℝ)*X 1 0+(2219276393/5000000000 : ℝ)*X 1 1+(2219276713/5000000000 : ℝ)*X 1 2+(2123250403/5000000000 : ℝ)*X 2 0+(2219276393/5000000000 : ℝ)*X 2 1+(2219276713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1082_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-5323954257469566892386482109699/8556250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69106843/100000000000000 : ℝ)*(lower2) + (31214333/20000000000000 : ℝ)*(upper4) + (130153549/100000000000000 : ℝ)*(upper5) + (48378244948411/1250000000000 : ℝ)*(major0) + (48378244948411/1250000000000 : ℝ)*(major1) + (48378244948411/1250000000000 : ℝ)*(major2) + (1657478257/12500000000000 : ℝ)*(sp1) + (802728943/20000000000000 : ℝ)*(sp3) + (1287891773436613/25000000000000 : ℝ)*(sp4) + (5151573981242247/100000000000000 : ℝ)*(sp5) + (5151414606728149/100000000000000 : ℝ)*(sp6) + (652417233108897/25000000000000 : ℝ)*(sp7) + (20147321851/100000000000000 : ℝ)*(sp8) + (86317170077/50000000000000 : ℝ)*(sp14) + (1304836473040151/50000000000000 : ℝ)*(f.failure) + (5151587241068303/100000000000000 : ℝ)*(f.sum) + (4401589363363/342250000000000000000000000 : ℝ)*base66 + (78715656256565733/17112500000000000000000000000000 : ℝ)*base67 + (91742246300503233/17112500000000000000000000000000 : ℝ)*base69 + (57007372312459267/17112500000000000000000000000000 : ℝ)*base72 + (1194260005939/273800000000000000000000000 : ℝ)*base73 + (57538606140115733/17112500000000000000000000000000 : ℝ)*base75 + (68820863511878233/17112500000000000000000000000000 : ℝ)*base77 + (80711564291634267/17112500000000000000000000000000 : ℝ)*base80 + (3832561605513/1369000000000000000000000000 : ℝ)*base82 + (1794601/625000000000000000000 : ℝ)*base90 + (1794601/625000000000000000000 : ℝ)*base92 + (1794601/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59253/100000 : ℝ) ≤ (202801253388815630623439421438741/342250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6979963/100000000000000 : ℝ)*(lower0) + (7383357/50000000000000 : ℝ)*(upper1) + (47428533/100000000000000 : ℝ)*(upper2) + (30313169/100000000000000 : ℝ)*(upper3) + (7920197/25000000000000 : ℝ)*(lower5) + (1966711160675251/50000000000000 : ℝ)*(major0) + (1966711160675251/50000000000000 : ℝ)*(major1) + (1966711160675251/50000000000000 : ℝ)*(major2) + (5194830008605761/100000000000000 : ℝ)*(sp0) + (324675424140243/6250000000000 : ℝ)*(sp1) + (32467627679519/625000000000 : ℝ)*(sp2) + (2652262868486391/100000000000000 : ℝ)*(sp3) + (9579882721/100000000000000 : ℝ)*(sp6) + (23222361873/100000000000000 : ℝ)*(sp9) + (2652262868486391/100000000000000 : ℝ)*(f.failure) + (5194830008605761/100000000000000 : ℝ)*(f.sum) + (1630544266543/427812500000000000000000000 : ℝ)*base66 + (4251933950722653753/684500000000000000000000000000000 : ℝ)*base67 + (10251666663248346247/684500000000000000000000000000000 : ℝ)*base70 + (2138116977795153753/684500000000000000000000000000000 : ℝ)*base71 + (54263454817779/3422500000000000000000000000 : ℝ)*base74 + (1901628079802846247/684500000000000000000000000000000 : ℝ)*base76 + (31071676436153753/684500000000000000000000000000000 : ℝ)*base77 + (3278176689456653753/684500000000000000000000000000000 : ℝ)*base79 + (51814885548993/6845000000000000000000000000 : ℝ)*base82 + (2808841/1250000000000000000000 : ℝ)*base90 + (2808841/1250000000000000000000 : ℝ)*base92 + (2808841/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79623/100000 : ℝ) ≤ (14730627579642336858188366305767/18500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (456283/312500000000 : ℝ)*(upper0) + (1923107/10000000000000 : ℝ)*(lower1) + (193665051/100000000000000 : ℝ)*(upper2) + (47374833/10000000000000 : ℝ)*(lower5) + (4401634863889931/100000000000000 : ℝ)*(major0) + (4401634863889931/100000000000000 : ℝ)*(major1) + (4401634863889931/100000000000000 : ℝ)*(major2) + (1462930609/50000000000000 : ℝ)*(sp0) + (278094372683/100000000000000 : ℝ)*(sp1) + (2157448697/1562500000000 : ℝ)*(sp3) + (290437587936151/5000000000000 : ℝ)*(sp8) + (1161695318042311/20000000000000 : ℝ)*(sp9) + (2904377342292119/50000000000000 : ℝ)*(sp10) + (593567059032867/20000000000000 : ℝ)*(sp11) + (1483986685940471/50000000000000 : ℝ)*(f.failure) + (2904377342292119/50000000000000 : ℝ)*(f.sum) + (18930019459311/6845000000000000000000000000 : ℝ)*base65 + (2947985737016162207/1369000000000000000000000000000000 : ℝ)*base68 + (2067028745022837793/1369000000000000000000000000000000 : ℝ)*base69 + (14691354109964162207/1369000000000000000000000000000000 : ℝ)*base72 + (92414112941589/6845000000000000000000000000 : ℝ)*base74 + (5479864887341162207/1369000000000000000000000000000000 : ℝ)*base76 + (9969844710007162207/1369000000000000000000000000000000 : ℝ)*base78 + (5596267217667837793/1369000000000000000000000000000000 : ℝ)*base79 + (34512183372159/6845000000000000000000000000 : ℝ)*base82 + (6268921/625000000000000000000 : ℝ)*base90 + (6268921/625000000000000000000 : ℝ)*base92 + (6268921/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-82989/100000 : ℝ) ≤ (-15352489483117115249238978374691/18500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155428971/50000000000000 : ℝ)*(upper3) + (296638423/50000000000000 : ℝ)*(lower4) + (9307963/10000000000000 : ℝ)*(upper5) + (4436318619973021/100000000000000 : ℝ)*(major0) + (4436318619973021/100000000000000 : ℝ)*(major1) + (4436318619973021/100000000000000 : ℝ)*(major2) + (713781711/5000000000000 : ℝ)*(sp4) + (7472991761/2000000000000 : ℝ)*(sp5) + (256895831479/20000000000000 : ℝ)*(sp6) + (702501853197/100000000000000 : ℝ)*(sp7) + (5908924865157021/100000000000000 : ℝ)*(sp12) + (5908565491203191/100000000000000 : ℝ)*(sp13) + (2953827330816923/50000000000000 : ℝ)*(sp14) + (149532887025721/5000000000000 : ℝ)*(sp15) + (2991360242367617/100000000000000 : ℝ)*(f.failure) + (5908939140791241/100000000000000 : ℝ)*(f.sum) + (6384719824783/3422500000000000000000000000 : ℝ)*base65 + (11937941148102607063/1369000000000000000000000000000000 : ℝ)*base67 + (13187560620315607063/1369000000000000000000000000000000 : ℝ)*base69 + (12555286868270607063/1369000000000000000000000000000000 : ℝ)*base71 + (6571895897469/1711250000000000000000000000 : ℝ)*base73 + (14516894585944607063/1369000000000000000000000000000000 : ℝ)*base75 + (12576267725559607063/1369000000000000000000000000000000 : ℝ)*base77 + (12793736847343607063/1369000000000000000000000000000000 : ℝ)*base79 + (25885743463541/6845000000000000000000000000 : ℝ)*base81 + (2540767/1250000000000000000000 : ℝ)*base90 + (2540767/1250000000000000000000 : ℝ)*base92 + (2540767/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1082_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59253/100000 : ℝ) else (79623/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82989/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1082_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1082_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59253/100000 : ℝ) else (79623/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82989/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1082_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1082_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4137/1024 : ℝ) ≤ p) (hpb : p ≤ (8275/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18538049/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59253/100000 : ℝ) else (79623/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82989/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1082_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
