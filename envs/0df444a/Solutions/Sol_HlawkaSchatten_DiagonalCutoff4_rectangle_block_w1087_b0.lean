-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1087_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:55:07.384633+00:00
-- url     : https://prove2.me/submissions/59dad114-ccfd-4ad0-ba3e-516743bd4129

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
theorem support_rectangle_w1087_s0_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909340633/10000000000 : ℝ)*x 0 + (3033564953/5000000000 : ℝ)*x 1 + (2386738533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909340633/10000000000 : ℝ)^1035 ≤ (2216116995273/20000000000000 : ℝ)^779 := by
    have hnat : (1909340633 : ℕ)^1035*20000000000000^779 ≤ 2216116995273^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909340633 10000000000 2216116995273 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3033564953/5000000000 : ℝ)^1035 ≤ (51483239392977/100000000000000 : ℝ)^779 := by
    have hnat : (3033564953 : ℕ)^1035*100000000000000^779 ≤ 51483239392977^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3033564953 5000000000 51483239392977 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386738533/5000000000 : ℝ)^1035 ≤ (37436175618859/100000000000000 : ℝ)^779 := by
    have hnat : (2386738533 : ℕ)^1035*100000000000000^779 ≤ 37436175618859^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386738533 5000000000 37436175618859 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909340633/10000000000 : ℝ), (3033564953/5000000000 : ℝ), (2386738533/5000000000 : ℝ)] ![(2216116995273/20000000000000 : ℝ), (51483239392977/100000000000000 : ℝ), (37436175618859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909340633/10000000000 : ℝ)|^1035 ≤ (2216116995273/20000000000000 : ℝ)^779
        have hw : |(-1909340633/10000000000 : ℝ)|=(1909340633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3033564953/5000000000 : ℝ)|^1035 ≤ (51483239392977/100000000000000 : ℝ)^779
        have hw : |(3033564953/5000000000 : ℝ)|=(3033564953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386738533/5000000000 : ℝ)|^1035 ≤ (37436175618859/100000000000000 : ℝ)^779
        have hw : |(2386738533/5000000000 : ℝ)|=(2386738533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s0_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (344993199/625000000 : ℝ)*x 0 + (-1326676623/5000000000 : ℝ)*x 1 + (4773477043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344993199/625000000 : ℝ)^1035 ≤ (45406921609081/100000000000000 : ℝ)^779 := by
    have hnat : (344993199 : ℕ)^1035*100000000000000^779 ≤ 45406921609081^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344993199 625000000 45406921609081 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1326676623/5000000000 : ℝ)^1035 ≤ (3431380599087/20000000000000 : ℝ)^779 := by
    have hnat : (1326676623 : ℕ)^1035*20000000000000^779 ≤ 3431380599087^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326676623 5000000000 3431380599087 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4773477043/10000000000 : ℝ)^1035 ≤ (9359043844801/25000000000000 : ℝ)^779 := by
    have hnat : (4773477043 : ℕ)^1035*25000000000000^779 ≤ 9359043844801^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4773477043 10000000000 9359043844801 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344993199/625000000 : ℝ), (-1326676623/5000000000 : ℝ), (4773477043/10000000000 : ℝ)] ![(45406921609081/100000000000000 : ℝ), (3431380599087/20000000000000 : ℝ), (9359043844801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344993199/625000000 : ℝ)|^1035 ≤ (45406921609081/100000000000000 : ℝ)^779
        have hw : |(344993199/625000000 : ℝ)|=(344993199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1326676623/5000000000 : ℝ)|^1035 ≤ (3431380599087/20000000000000 : ℝ)^779
        have hw : |(-1326676623/5000000000 : ℝ)|=(1326676623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4773477043/10000000000 : ℝ)|^1035 ≤ (9359043844801/25000000000000 : ℝ)^779
        have hw : |(4773477043/10000000000 : ℝ)|=(4773477043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s0_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1103978121/2000000000 : ℝ)*x 0 + (477347747/1000000000 : ℝ)*x 1 + (-530670693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103978121/2000000000 : ℝ)^1035 ≤ (22703457640493/50000000000000 : ℝ)^779 := by
    have hnat : (1103978121 : ℕ)^1035*50000000000000^779 ≤ 22703457640493^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103978121 2000000000 22703457640493 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477347747/1000000000 : ℝ)^1035 ≤ (1871808991423/5000000000000 : ℝ)^779 := by
    have hnat : (477347747 : ℕ)^1035*5000000000000^779 ≤ 1871808991423^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477347747 1000000000 1871808991423 5000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530670693/2000000000 : ℝ)^1035 ≤ (17156904876877/100000000000000 : ℝ)^779 := by
    have hnat : (530670693 : ℕ)^1035*100000000000000^779 ≤ 17156904876877^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530670693 2000000000 17156904876877 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103978121/2000000000 : ℝ), (477347747/1000000000 : ℝ), (-530670693/2000000000 : ℝ)] ![(22703457640493/50000000000000 : ℝ), (1871808991423/5000000000000 : ℝ), (17156904876877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103978121/2000000000 : ℝ)|^1035 ≤ (22703457640493/50000000000000 : ℝ)^779
        have hw : |(1103978121/2000000000 : ℝ)|=(1103978121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(477347747/1000000000 : ℝ)|^1035 ≤ (1871808991423/5000000000000 : ℝ)^779
        have hw : |(477347747/1000000000 : ℝ)|=(477347747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-530670693/2000000000 : ℝ)|^1035 ≤ (17156904876877/100000000000000 : ℝ)^779
        have hw : |(-530670693/2000000000 : ℝ)|=(530670693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s0_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (525684611/1250000000 : ℝ)*x 0 + (312376583/1000000000 : ℝ)*x 1 + (5669718249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525684611/1250000000 : ℝ)^1035 ≤ (3163668672417/10000000000000 : ℝ)^779 := by
    have hnat : (525684611 : ℕ)^1035*10000000000000^779 ≤ 3163668672417^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525684611 1250000000 3163668672417 10000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312376583/1000000000 : ℝ)^1035 ≤ (21311619440283/100000000000000 : ℝ)^779 := by
    have hnat : (312376583 : ℕ)^1035*100000000000000^779 ≤ 21311619440283^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312376583 1000000000 21311619440283 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5669718249/10000000000 : ℝ)^1035 ≤ (47051693820947/100000000000000 : ℝ)^779 := by
    have hnat : (5669718249 : ℕ)^1035*100000000000000^779 ≤ 47051693820947^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669718249 10000000000 47051693820947 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525684611/1250000000 : ℝ), (312376583/1000000000 : ℝ), (5669718249/10000000000 : ℝ)] ![(3163668672417/10000000000000 : ℝ), (21311619440283/100000000000000 : ℝ), (47051693820947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525684611/1250000000 : ℝ)|^1035 ≤ (3163668672417/10000000000000 : ℝ)^779
        have hw : |(525684611/1250000000 : ℝ)|=(525684611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312376583/1000000000 : ℝ)|^1035 ≤ (21311619440283/100000000000000 : ℝ)^779
        have hw : |(312376583/1000000000 : ℝ)|=(312376583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5669718249/10000000000 : ℝ)|^1035 ≤ (47051693820947/100000000000000 : ℝ)^779
        have hw : |(5669718249/10000000000 : ℝ)|=(5669718249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s0_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-119665683/625000000 : ℝ)*x 0 + (2403436467/5000000000 : ℝ)*x 1 + (6032563639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119665683/625000000 : ℝ)^1035 ≤ (11121548670411/100000000000000 : ℝ)^779 := by
    have hnat : (119665683 : ℕ)^1035*100000000000000^779 ≤ 11121548670411^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119665683 625000000 11121548670411 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403436467/5000000000 : ℝ)^1035 ≤ (7556910679307/20000000000000 : ℝ)^779 := by
    have hnat : (2403436467 : ℕ)^1035*20000000000000^779 ≤ 7556910679307^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403436467 5000000000 7556910679307 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6032563639/10000000000 : ℝ)^1035 ≤ (5109389791593/10000000000000 : ℝ)^779 := by
    have hnat : (6032563639 : ℕ)^1035*10000000000000^779 ≤ 5109389791593^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032563639 10000000000 5109389791593 10000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119665683/625000000 : ℝ), (2403436467/5000000000 : ℝ), (6032563639/10000000000 : ℝ)] ![(11121548670411/100000000000000 : ℝ), (7556910679307/20000000000000 : ℝ), (5109389791593/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119665683/625000000 : ℝ)|^1035 ≤ (11121548670411/100000000000000 : ℝ)^779
        have hw : |(-119665683/625000000 : ℝ)|=(119665683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2403436467/5000000000 : ℝ)|^1035 ≤ (7556910679307/20000000000000 : ℝ)^779
        have hw : |(2403436467/5000000000 : ℝ)|=(2403436467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6032563639/10000000000 : ℝ)|^1035 ≤ (5109389791593/10000000000000 : ℝ)^779
        have hw : |(6032563639/10000000000 : ℝ)|=(6032563639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s0_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1292164947/2500000000 : ℝ)*x 0 + (-1394269453/10000000000 : ℝ)*x 1 + (6032562501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292164947/2500000000 : ℝ)^1035 ≤ (2080445604399/5000000000000 : ℝ)^779 := by
    have hnat : (1292164947 : ℕ)^1035*5000000000000^779 ≤ 2080445604399^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292164947 2500000000 2080445604399 5000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394269453/10000000000 : ℝ)^1035 ≤ (7297202785429/100000000000000 : ℝ)^779 := by
    have hnat : (1394269453 : ℕ)^1035*100000000000000^779 ≤ 7297202785429^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394269453 10000000000 7297202785429 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6032562501/10000000000 : ℝ)^1035 ≤ (25546942554983/50000000000000 : ℝ)^779 := by
    have hnat : (6032562501 : ℕ)^1035*50000000000000^779 ≤ 25546942554983^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032562501 10000000000 25546942554983 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292164947/2500000000 : ℝ), (-1394269453/10000000000 : ℝ), (6032562501/10000000000 : ℝ)] ![(2080445604399/5000000000000 : ℝ), (7297202785429/100000000000000 : ℝ), (25546942554983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292164947/2500000000 : ℝ)|^1035 ≤ (2080445604399/5000000000000 : ℝ)^779
        have hw : |(1292164947/2500000000 : ℝ)|=(1292164947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1394269453/10000000000 : ℝ)|^1035 ≤ (7297202785429/100000000000000 : ℝ)^779
        have hw : |(-1394269453/10000000000 : ℝ)|=(1394269453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6032562501/10000000000 : ℝ)|^1035 ≤ (25546942554983/50000000000000 : ℝ)^779
        have hw : |(6032562501/10000000000 : ℝ)|=(6032562501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s0_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1292165009/2500000000 : ℝ)*x 0 + (603256361/1000000000 : ℝ)*x 1 + (-1394267277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292165009/2500000000 : ℝ)^1035 ≤ (41608914740527/100000000000000 : ℝ)^779 := by
    have hnat : (1292165009 : ℕ)^1035*100000000000000^779 ≤ 41608914740527^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292165009 2500000000 41608914740527 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603256361/1000000000 : ℝ)^1035 ≤ (6386737198699/12500000000000 : ℝ)^779 := by
    have hnat : (603256361 : ℕ)^1035*12500000000000^779 ≤ 6386737198699^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603256361 1000000000 6386737198699 12500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394267277/10000000000 : ℝ)^1035 ≤ (3648593827149/50000000000000 : ℝ)^779 := by
    have hnat : (1394267277 : ℕ)^1035*50000000000000^779 ≤ 3648593827149^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394267277 10000000000 3648593827149 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292165009/2500000000 : ℝ), (603256361/1000000000 : ℝ), (-1394267277/10000000000 : ℝ)] ![(41608914740527/100000000000000 : ℝ), (6386737198699/12500000000000 : ℝ), (3648593827149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292165009/2500000000 : ℝ)|^1035 ≤ (41608914740527/100000000000000 : ℝ)^779
        have hw : |(1292165009/2500000000 : ℝ)|=(1292165009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603256361/1000000000 : ℝ)|^1035 ≤ (6386737198699/12500000000000 : ℝ)^779
        have hw : |(603256361/1000000000 : ℝ)|=(603256361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1394267277/10000000000 : ℝ)|^1035 ≤ (3648593827149/50000000000000 : ℝ)^779
        have hw : |(-1394267277/10000000000 : ℝ)|=(1394267277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s0_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2107962279/5000000000 : ℝ)*x 0 + (350249573/625000000 : ℝ)*x 1 + (3191793949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107962279/5000000000 : ℝ)^1035 ≤ (31741152787221/100000000000000 : ℝ)^779 := by
    have hnat : (2107962279 : ℕ)^1035*100000000000000^779 ≤ 31741152787221^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107962279 5000000000 31741152787221 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350249573/625000000 : ℝ)^1035 ≤ (46328395216837/100000000000000 : ℝ)^779 := by
    have hnat : (350249573 : ℕ)^1035*100000000000000^779 ≤ 46328395216837^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350249573 625000000 46328395216837 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3191793949/10000000000 : ℝ)^1035 ≤ (21930451978587/100000000000000 : ℝ)^779 := by
    have hnat : (3191793949 : ℕ)^1035*100000000000000^779 ≤ 21930451978587^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191793949 10000000000 21930451978587 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107962279/5000000000 : ℝ), (350249573/625000000 : ℝ), (3191793949/10000000000 : ℝ)] ![(31741152787221/100000000000000 : ℝ), (46328395216837/100000000000000 : ℝ), (21930451978587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107962279/5000000000 : ℝ)|^1035 ≤ (31741152787221/100000000000000 : ℝ)^779
        have hw : |(2107962279/5000000000 : ℝ)|=(2107962279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350249573/625000000 : ℝ)|^1035 ≤ (46328395216837/100000000000000 : ℝ)^779
        have hw : |(350249573/625000000 : ℝ)|=(350249573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3191793949/10000000000 : ℝ)|^1035 ≤ (21930451978587/100000000000000 : ℝ)^779
        have hw : |(3191793949/10000000000 : ℝ)|=(3191793949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (37/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28027/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8279/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8279 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8279*1^2048 ≤ 0^2048*1^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8279/2048 : ℝ) ≤ (2462267808589156243/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8279 ≤ (2462267808589156243/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8279*100000000000000000000^2048 ≤ 2462267808589156243^2048*5^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2462267808589156243 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2462267808589156243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8279 := by
      have hnat : (1 : ℕ)^2048*1^8279 ≤ 1^8279*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102462267808589156243/100000000000000000000 : ℝ) ≤ (10060353427992331/10000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (102462267808589156243/100000000000000000000 : ℝ)^2048 ≤ (10060353427992331/10000000000000000 : ℝ)^8279 := by
      have hnat : (102462267808589156243 : ℕ)^2048*10000000000000000^8279 ≤ 10060353427992331^8279*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102462267808589156243 100000000000000000000 10060353427992331 10000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060353427992331/10000000000000000 : ℝ)) (X := (102462267808589156243/100000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52462267808589156243/50000000000000000000 : ℝ) ≤ (5060353427992331/5000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (52462267808589156243/50000000000000000000 : ℝ)^2048 ≤ (5060353427992331/5000000000000000 : ℝ)^8279 := by
      have hnat : (52462267808589156243 : ℕ)^2048*5000000000000000^8279 ≤ 5060353427992331^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52462267808589156243 50000000000000000000 5060353427992331 5000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060353427992331/5000000000000000 : ℝ)) (X := (52462267808589156243/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60353427992331/4000000000000000 : ℝ)*(0 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60353427992331/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2462267808589156243/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60353427992331/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (1 : ℝ)+(60353427992331/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060353427992331/10000000000000000 : ℝ) by norm_num, show 1+(2462267808589156243/100000000000000000000 : ℝ)+(0 : ℝ)=(102462267808589156243/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2462267808589156243/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60353427992331/4000000000000000 : ℝ)*(2/5 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60353427992331/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060353427992331/5000000000000000 : ℝ) by norm_num, show 1+2*(2462267808589156243/100000000000000000000 : ℝ)=(52462267808589156243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60353427992331/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60353427992331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60353427992331/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60353427992331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60353427992331/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60353427992331/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1909340633/10000000000 : ℝ)*X 0 0+(3033564953/5000000000 : ℝ)*X 0 1+(2386738533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((344993199/625000000 : ℝ)*X 1 0+(-1326676623/5000000000 : ℝ)*X 1 1+(4773477043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103978121/2000000000 : ℝ)*X 2 0+(477347747/1000000000 : ℝ)*X 2 1+(-530670693/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525684611/1250000000 : ℝ)*X 0 0+(312376583/1000000000 : ℝ)*X 0 1+(5669718249/10000000000 : ℝ)*X 0 2+(525684611/1250000000 : ℝ)*X 1 0+(312376583/1000000000 : ℝ)*X 1 1+(5669718249/10000000000 : ℝ)*X 1 2+(525684611/1250000000 : ℝ)*X 2 0+(312376583/1000000000 : ℝ)*X 2 1+(5669718249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-119665683/625000000 : ℝ)*X 0 0+(2403436467/5000000000 : ℝ)*X 0 1+(6032563639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292164947/2500000000 : ℝ)*X 1 0+(-1394269453/10000000000 : ℝ)*X 1 1+(6032562501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292165009/2500000000 : ℝ)*X 2 0+(603256361/1000000000 : ℝ)*X 2 1+(-1394267277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2107962279/5000000000 : ℝ)*X 0 0+(350249573/625000000 : ℝ)*X 0 1+(3191793949/10000000000 : ℝ)*X 0 2+(2107962279/5000000000 : ℝ)*X 1 0+(350249573/625000000 : ℝ)*X 1 1+(3191793949/10000000000 : ℝ)*X 1 2+(2107962279/5000000000 : ℝ)*X 2 0+(350249573/625000000 : ℝ)*X 2 1+(3191793949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107828493195728055200061/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (757421/800000000000 : ℝ)*(base1) + (991254861/100000000000000 : ℝ)*(base19) + (433366099/50000000000000 : ℝ)*(base23) + (43439137/100000000000000 : ℝ)*(base24) + (224487501/100000000000000 : ℝ)*(upper3) + (145724109971241/25000000000000 : ℝ)*(major0) + (145724109971241/25000000000000 : ℝ)*(major1) + (145724109971241/25000000000000 : ℝ)*(major2) + (193252023777187/25000000000000 : ℝ)*(sp0) + (193252241978539/25000000000000 : ℝ)*(sp1) + (386504524498841/50000000000000 : ℝ)*(sp2) + (196390590209723/50000000000000 : ℝ)*(sp3) + (979368947/50000000000000 : ℝ)*(sp4) + (1501732509/100000000000000 : ℝ)*(sp7) + (19639138841479/5000000000000 : ℝ)*(f.failure) + (773009959169017/100000000000000 : ℝ)*(f.sum) + (68924930852771/50000000000000000000000000000 : ℝ)*base65 + (631204040952771/100000000000000000000000000000 : ℝ)*base67 + (544238005652771/100000000000000000000000000000 : ℝ)*base69 + (706362701152771/100000000000000000000000000000 : ℝ)*base71 + (47070862752771/50000000000000000000000000000 : ℝ)*base73 + (1121146898252771/100000000000000000000000000000 : ℝ)*base75 + (609825010552771/100000000000000000000000000000 : ℝ)*base77 + (998459455352771/100000000000000000000000000000 : ℝ)*base79 + (47975280302771/50000000000000000000000000000 : ℝ)*base81 + (1799851/500000000000000000000 : ℝ)*base90 + (1799851/500000000000000000000 : ℝ)*base92 + (1799851/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64030768065389513767047/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241321973/100000000000000 : ℝ)*(base19) + (39575433/6250000000000 : ℝ)*(base23) + (60360123/25000000000000 : ℝ)*(base39) + (1448719/50000000000000 : ℝ)*(base45) + (3380867/10000000000000 : ℝ)*(upper2) + (225578041/100000000000000 : ℝ)*(upper5) + (61521260101113/10000000000000 : ℝ)*(major0) + (61521260101113/10000000000000 : ℝ)*(major1) + (307606179785319/50000000000000 : ℝ)*(major2) + (778987669/100000000000000 : ℝ)*(sp2) + (815865963484783/100000000000000 : ℝ)*(sp4) + (81586572216281/10000000000000 : ℝ)*(sp5) + (407932396365339/50000000000000 : ℝ)*(sp6) + (20727945586131/5000000000000 : ℝ)*(sp7) + (20727945586131/5000000000000 : ℝ)*(f.failure) + (203966551231319/25000000000000 : ℝ)*(f.sum) + (112646083502651/50000000000000000000000000000 : ℝ)*base65 + (611006061988589/200000000000000000000000000000 : ℝ)*base67 + (256100379884403/40000000000000000000000000000 : ℝ)*base69 + (438293510388589/200000000000000000000000000000 : ℝ)*base71 + (20261111197349/50000000000000000000000000000 : ℝ)*base74 + (313413080964403/40000000000000000000000000000 : ℝ)*base75 + (311388204044403/40000000000000000000000000000 : ℝ)*base77 + (165469441764403/40000000000000000000000000000 : ℝ)*base79 + (33169941215597/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7239/500000000000000000000 : ℝ)*base90 + (7239/500000000000000000000 : ℝ)*base92 + (7239/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1087_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (37/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1087_s1_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-105898611/500000000 : ℝ)*x 0 + (2858229637/5000000000 : ℝ)*x 1 + (2495276677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105898611/500000000 : ℝ)^1035 ≤ (12717443921419/100000000000000 : ℝ)^779 := by
    have hnat : (105898611 : ℕ)^1035*100000000000000^779 ≤ 12717443921419^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105898611 500000000 12717443921419 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2858229637/5000000000 : ℝ)^1035 ≤ (2378387781671/5000000000000 : ℝ)^779 := by
    have hnat : (2858229637 : ℕ)^1035*5000000000000^779 ≤ 2378387781671^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858229637 5000000000 2378387781671 5000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495276677/5000000000 : ℝ)^1035 ≤ (2482175027237/6250000000000 : ℝ)^779 := by
    have hnat : (2495276677 : ℕ)^1035*6250000000000^779 ≤ 2482175027237^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495276677 5000000000 2482175027237 6250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105898611/500000000 : ℝ), (2858229637/5000000000 : ℝ), (2495276677/5000000000 : ℝ)] ![(12717443921419/100000000000000 : ℝ), (2378387781671/5000000000000 : ℝ), (2482175027237/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105898611/500000000 : ℝ)|^1035 ≤ (12717443921419/100000000000000 : ℝ)^779
        have hw : |(-105898611/500000000 : ℝ)|=(105898611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2858229637/5000000000 : ℝ)|^1035 ≤ (2378387781671/5000000000000 : ℝ)^779
        have hw : |(2858229637/5000000000 : ℝ)|=(2858229637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2495276677/5000000000 : ℝ)|^1035 ≤ (2482175027237/6250000000000 : ℝ)^779
        have hw : |(2495276677/5000000000 : ℝ)|=(2495276677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2711074813/5000000000 : ℝ)*x 0 + (-2510828797/10000000000 : ℝ)*x 1 + (4990553593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711074813/5000000000 : ℝ)^1035 ≤ (22170895085473/50000000000000 : ℝ)^779 := by
    have hnat : (2711074813 : ℕ)^1035*50000000000000^779 ≤ 22170895085473^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711074813 5000000000 22170895085473 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510828797/10000000000 : ℝ)^1035 ≤ (3985851715267/25000000000000 : ℝ)^779 := by
    have hnat : (2510828797 : ℕ)^1035*25000000000000^779 ≤ 3985851715267^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510828797 10000000000 3985851715267 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4990553593/10000000000 : ℝ)^1035 ≤ (9928700740697/25000000000000 : ℝ)^779 := by
    have hnat : (4990553593 : ℕ)^1035*25000000000000^779 ≤ 9928700740697^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990553593 10000000000 9928700740697 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711074813/5000000000 : ℝ), (-2510828797/10000000000 : ℝ), (4990553593/10000000000 : ℝ)] ![(22170895085473/50000000000000 : ℝ), (3985851715267/25000000000000 : ℝ), (9928700740697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711074813/5000000000 : ℝ)|^1035 ≤ (22170895085473/50000000000000 : ℝ)^779
        have hw : |(2711074813/5000000000 : ℝ)|=(2711074813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2510828797/10000000000 : ℝ)|^1035 ≤ (3985851715267/25000000000000 : ℝ)^779
        have hw : |(-2510828797/10000000000 : ℝ)|=(2510828797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4990553593/10000000000 : ℝ)|^1035 ≤ (9928700740697/25000000000000 : ℝ)^779
        have hw : |(4990553593/10000000000 : ℝ)|=(4990553593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2711075237/5000000000 : ℝ)*x 0 + (4990552713/10000000000 : ℝ)*x 1 + (-313853601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711075237/5000000000 : ℝ)^1035 ≤ (22170899692391/50000000000000 : ℝ)^779 := by
    have hnat : (2711075237 : ℕ)^1035*50000000000000^779 ≤ 22170899692391^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711075237 5000000000 22170899692391 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4990552713/10000000000 : ℝ)^1035 ≤ (39714793658369/100000000000000 : ℝ)^779 := by
    have hnat : (4990552713 : ℕ)^1035*100000000000000^779 ≤ 39714793658369^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990552713 10000000000 39714793658369 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313853601/1250000000 : ℝ)^1035 ≤ (15943406953871/100000000000000 : ℝ)^779 := by
    have hnat : (313853601 : ℕ)^1035*100000000000000^779 ≤ 15943406953871^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313853601 1250000000 15943406953871 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711075237/5000000000 : ℝ), (4990552713/10000000000 : ℝ), (-313853601/1250000000 : ℝ)] ![(22170899692391/50000000000000 : ℝ), (39714793658369/100000000000000 : ℝ), (15943406953871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711075237/5000000000 : ℝ)|^1035 ≤ (22170899692391/50000000000000 : ℝ)^779
        have hw : |(2711075237/5000000000 : ℝ)|=(2711075237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4990552713/10000000000 : ℝ)|^1035 ≤ (39714793658369/100000000000000 : ℝ)^779
        have hw : |(4990552713/10000000000 : ℝ)|=(4990552713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-313853601/1250000000 : ℝ)|^1035 ≤ (15943406953871/100000000000000 : ℝ)^779
        have hw : |(-313853601/1250000000 : ℝ)|=(313853601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4322061281/10000000000 : ℝ)*x 0 + (229163027/625000000 : ℝ)*x 1 + (2547607473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322061281/10000000000 : ℝ)^1035 ≤ (6561442367159/20000000000000 : ℝ)^779 := by
    have hnat : (4322061281 : ℕ)^1035*20000000000000^779 ≤ 6561442367159^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322061281 10000000000 6561442367159 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229163027/625000000 : ℝ)^1035 ≤ (26367583844777/100000000000000 : ℝ)^779 := by
    have hnat : (229163027 : ℕ)^1035*100000000000000^779 ≤ 26367583844777^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229163027 625000000 26367583844777 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547607473/5000000000 : ℝ)^1035 ≤ (40825204296153/100000000000000 : ℝ)^779 := by
    have hnat : (2547607473 : ℕ)^1035*100000000000000^779 ≤ 40825204296153^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547607473 5000000000 40825204296153 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322061281/10000000000 : ℝ), (229163027/625000000 : ℝ), (2547607473/5000000000 : ℝ)] ![(6561442367159/20000000000000 : ℝ), (26367583844777/100000000000000 : ℝ), (40825204296153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322061281/10000000000 : ℝ)|^1035 ≤ (6561442367159/20000000000000 : ℝ)^779
        have hw : |(4322061281/10000000000 : ℝ)|=(4322061281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229163027/625000000 : ℝ)|^1035 ≤ (26367583844777/100000000000000 : ℝ)^779
        have hw : |(229163027/625000000 : ℝ)|=(229163027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547607473/5000000000 : ℝ)|^1035 ≤ (40825204296153/100000000000000 : ℝ)^779
        have hw : |(2547607473/5000000000 : ℝ)|=(2547607473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059431041/5000000000 : ℝ)*x 0 + (1000134827/2000000000 : ℝ)*x 1 + (5706131781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059431041/5000000000 : ℝ)^1035 ≤ (6362271770703/50000000000000 : ℝ)^779 := by
    have hnat : (1059431041 : ℕ)^1035*50000000000000^779 ≤ 6362271770703^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059431041 5000000000 6362271770703 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000134827/2000000000 : ℝ)^1035 ≤ (39821845150563/100000000000000 : ℝ)^779 := by
    have hnat : (1000134827 : ℕ)^1035*100000000000000^779 ≤ 39821845150563^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000134827 2000000000 39821845150563 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5706131781/10000000000 : ℝ)^1035 ≤ (47453611300113/100000000000000 : ℝ)^779 := by
    have hnat : (5706131781 : ℕ)^1035*100000000000000^779 ≤ 47453611300113^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706131781 10000000000 47453611300113 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059431041/5000000000 : ℝ), (1000134827/2000000000 : ℝ), (5706131781/10000000000 : ℝ)] ![(6362271770703/50000000000000 : ℝ), (39821845150563/100000000000000 : ℝ), (47453611300113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059431041/5000000000 : ℝ)|^1035 ≤ (6362271770703/50000000000000 : ℝ)^779
        have hw : |(-1059431041/5000000000 : ℝ)|=(1059431041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000134827/2000000000 : ℝ)|^1035 ≤ (39821845150563/100000000000000 : ℝ)^779
        have hw : |(1000134827/2000000000 : ℝ)|=(1000134827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5706131781/10000000000 : ℝ)|^1035 ≤ (47453611300113/100000000000000 : ℝ)^779
        have hw : |(5706131781/10000000000 : ℝ)|=(5706131781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (523656147/1000000000 : ℝ)*x 0 + (-897623853/5000000000 : ℝ)*x 1 + (570613411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523656147/1000000000 : ℝ)^1035 ≤ (42336734738557/100000000000000 : ℝ)^779 := by
    have hnat : (523656147 : ℕ)^1035*100000000000000^779 ≤ 42336734738557^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523656147 1000000000 42336734738557 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897623853/5000000000 : ℝ)^1035 ≤ (5104814111383/50000000000000 : ℝ)^779 := by
    have hnat : (897623853 : ℕ)^1035*50000000000000^779 ≤ 5104814111383^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897623853 5000000000 5104814111383 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570613411/1000000000 : ℝ)^1035 ≤ (23726818516837/50000000000000 : ℝ)^779 := by
    have hnat : (570613411 : ℕ)^1035*50000000000000^779 ≤ 23726818516837^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570613411 1000000000 23726818516837 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523656147/1000000000 : ℝ), (-897623853/5000000000 : ℝ), (570613411/1000000000 : ℝ)] ![(42336734738557/100000000000000 : ℝ), (5104814111383/50000000000000 : ℝ), (23726818516837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523656147/1000000000 : ℝ)|^1035 ≤ (42336734738557/100000000000000 : ℝ)^779
        have hw : |(523656147/1000000000 : ℝ)|=(523656147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-897623853/5000000000 : ℝ)|^1035 ≤ (5104814111383/50000000000000 : ℝ)^779
        have hw : |(-897623853/5000000000 : ℝ)|=(897623853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570613411/1000000000 : ℝ)|^1035 ≤ (23726818516837/50000000000000 : ℝ)^779
        have hw : |(570613411/1000000000 : ℝ)|=(570613411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5236559379/10000000000 : ℝ)*x 0 + (1141227291/2000000000 : ℝ)*x 1 + (-112202953/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236559379/10000000000 : ℝ)^1035 ≤ (4233671227761/10000000000000 : ℝ)^779 := by
    have hnat : (5236559379 : ℕ)^1035*10000000000000^779 ≤ 4233671227761^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236559379 10000000000 4233671227761 10000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141227291/2000000000 : ℝ)^1035 ≤ (1898146517761/4000000000000 : ℝ)^779 := by
    have hnat : (1141227291 : ℕ)^1035*4000000000000^779 ≤ 1898146517761^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141227291 2000000000 1898146517761 4000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112202953/625000000 : ℝ)^1035 ≤ (5104812381073/50000000000000 : ℝ)^779 := by
    have hnat : (112202953 : ℕ)^1035*50000000000000^779 ≤ 5104812381073^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112202953 625000000 5104812381073 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236559379/10000000000 : ℝ), (1141227291/2000000000 : ℝ), (-112202953/625000000 : ℝ)] ![(4233671227761/10000000000000 : ℝ), (1898146517761/4000000000000 : ℝ), (5104812381073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236559379/10000000000 : ℝ)|^1035 ≤ (4233671227761/10000000000000 : ℝ)^779
        have hw : |(5236559379/10000000000 : ℝ)|=(5236559379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141227291/2000000000 : ℝ)|^1035 ≤ (1898146517761/4000000000000 : ℝ)^779
        have hw : |(1141227291/2000000000 : ℝ)|=(1141227291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112202953/625000000 : ℝ)|^1035 ≤ (5104812381073/50000000000000 : ℝ)^779
        have hw : |(-112202953/625000000 : ℝ)|=(112202953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4323807397/10000000000 : ℝ)*x 0 + (5075293629/10000000000 : ℝ)*x 1 + (921732161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323807397/10000000000 : ℝ)^1035 ≤ (16412411401587/50000000000000 : ℝ)^779 := by
    have hnat : (4323807397 : ℕ)^1035*50000000000000^779 ≤ 16412411401587^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323807397 10000000000 16412411401587 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075293629/10000000000 : ℝ)^1035 ≤ (20306633483823/50000000000000 : ℝ)^779 := by
    have hnat : (5075293629 : ℕ)^1035*50000000000000^779 ≤ 20306633483823^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075293629 10000000000 20306633483823 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921732161/2500000000 : ℝ)^1035 ≤ (6640477553571/25000000000000 : ℝ)^779 := by
    have hnat : (921732161 : ℕ)^1035*25000000000000^779 ≤ 6640477553571^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921732161 2500000000 6640477553571 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323807397/10000000000 : ℝ), (5075293629/10000000000 : ℝ), (921732161/2500000000 : ℝ)] ![(16412411401587/50000000000000 : ℝ), (20306633483823/50000000000000 : ℝ), (6640477553571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323807397/10000000000 : ℝ)|^1035 ≤ (16412411401587/50000000000000 : ℝ)^779
        have hw : |(4323807397/10000000000 : ℝ)|=(4323807397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075293629/10000000000 : ℝ)|^1035 ≤ (20306633483823/50000000000000 : ℝ)^779
        have hw : |(5075293629/10000000000 : ℝ)|=(5075293629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921732161/2500000000 : ℝ)|^1035 ≤ (6640477553571/25000000000000 : ℝ)^779
        have hw : |(921732161/2500000000 : ℝ)|=(921732161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_8 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (3960613/5000000000 : ℝ)*x 0 + (109798901/200000000 : ℝ)*x 1 + (6368860081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3960613/5000000000 : ℝ)^1035 ≤ (3789863637/50000000000000 : ℝ)^779 := by
    have hnat : (3960613 : ℕ)^1035*50000000000000^779 ≤ 3789863637^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3960613 5000000000 3789863637 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109798901/200000000 : ℝ)^1035 ≤ (2253996093141/5000000000000 : ℝ)^779 := by
    have hnat : (109798901 : ℕ)^1035*5000000000000^779 ≤ 2253996093141^779*200000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109798901 200000000 2253996093141 5000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6368860081/10000000000 : ℝ)^1035 ≤ (2745624920227/5000000000000 : ℝ)^779 := by
    have hnat : (6368860081 : ℕ)^1035*5000000000000^779 ≤ 2745624920227^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6368860081 10000000000 2745624920227 5000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3960613/5000000000 : ℝ), (109798901/200000000 : ℝ), (6368860081/10000000000 : ℝ)] ![(3789863637/50000000000000 : ℝ), (2253996093141/5000000000000 : ℝ), (2745624920227/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3960613/5000000000 : ℝ)|^1035 ≤ (3789863637/50000000000000 : ℝ)^779
        have hw : |(3960613/5000000000 : ℝ)|=(3960613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109798901/200000000 : ℝ)|^1035 ≤ (2253996093141/5000000000000 : ℝ)^779
        have hw : |(109798901/200000000 : ℝ)|=(109798901/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6368860081/10000000000 : ℝ)|^1035 ≤ (2745624920227/5000000000000 : ℝ)^779
        have hw : |(6368860081/10000000000 : ℝ)|=(6368860081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_9 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (96835561/1000000000 : ℝ)*x 0 + (-55565889/125000000 : ℝ)*x 1 + (277256341/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96835561/1000000000 : ℝ)^1035 ≤ (2247962815071/50000000000000 : ℝ)^779 := by
    have hnat : (96835561 : ℕ)^1035*50000000000000^779 ≤ 2247962815071^779*1000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96835561 1000000000 2247962815071 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55565889/125000000 : ℝ)^1035 ≤ (8513895551103/25000000000000 : ℝ)^779 := by
    have hnat : (55565889 : ℕ)^1035*25000000000000^779 ≤ 8513895551103^779*125000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55565889 125000000 8513895551103 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277256341/400000000 : ℝ)^1035 ≤ (2457939686009/4000000000000 : ℝ)^779 := by
    have hnat : (277256341 : ℕ)^1035*4000000000000^779 ≤ 2457939686009^779*400000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277256341 400000000 2457939686009 4000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(96835561/1000000000 : ℝ), (-55565889/125000000 : ℝ), (277256341/400000000 : ℝ)] ![(2247962815071/50000000000000 : ℝ), (8513895551103/25000000000000 : ℝ), (2457939686009/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(96835561/1000000000 : ℝ)|^1035 ≤ (2247962815071/50000000000000 : ℝ)^779
        have hw : |(96835561/1000000000 : ℝ)|=(96835561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55565889/125000000 : ℝ)|^1035 ≤ (8513895551103/25000000000000 : ℝ)^779
        have hw : |(-55565889/125000000 : ℝ)|=(55565889/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277256341/400000000 : ℝ)|^1035 ≤ (2457939686009/4000000000000 : ℝ)^779
        have hw : |(277256341/400000000 : ℝ)|=(277256341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_10 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (193669739/2000000000 : ℝ)*x 0 + (6931393357/10000000000 : ℝ)*x 1 + (-4445292863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193669739/2000000000 : ℝ)^1035 ≤ (4495882974271/100000000000000 : ℝ)^779 := by
    have hnat : (193669739 : ℕ)^1035*100000000000000^779 ≤ 4495882974271^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193669739 2000000000 4495882974271 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6931393357/10000000000 : ℝ)^1035 ≤ (12289662698583/20000000000000 : ℝ)^779 := by
    have hnat : (6931393357 : ℕ)^1035*20000000000000^779 ≤ 12289662698583^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6931393357 10000000000 12289662698583 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4445292863/10000000000 : ℝ)^1035 ≤ (17027901760193/50000000000000 : ℝ)^779 := by
    have hnat : (4445292863 : ℕ)^1035*50000000000000^779 ≤ 17027901760193^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445292863 10000000000 17027901760193 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(193669739/2000000000 : ℝ), (6931393357/10000000000 : ℝ), (-4445292863/10000000000 : ℝ)] ![(4495882974271/100000000000000 : ℝ), (12289662698583/20000000000000 : ℝ), (17027901760193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(193669739/2000000000 : ℝ)|^1035 ≤ (4495882974271/100000000000000 : ℝ)^779
        have hw : |(193669739/2000000000 : ℝ)|=(193669739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6931393357/10000000000 : ℝ)|^1035 ≤ (12289662698583/20000000000000 : ℝ)^779
        have hw : |(6931393357/10000000000 : ℝ)|=(6931393357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4445292863/10000000000 : ℝ)|^1035 ≤ (17027901760193/50000000000000 : ℝ)^779
        have hw : |(-4445292863/10000000000 : ℝ)|=(4445292863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s1_11 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (48062653/250000000 : ℝ)*x 0 + (2912689441/5000000000 : ℝ)*x 1 + (5021476489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48062653/250000000 : ℝ)^1035 ≤ (1397776526453/12500000000000 : ℝ)^779 := by
    have hnat : (48062653 : ℕ)^1035*12500000000000^779 ≤ 1397776526453^779*250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48062653 250000000 1397776526453 12500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2912689441/5000000000 : ℝ)^1035 ≤ (48775698317293/100000000000000 : ℝ)^779 := by
    have hnat : (2912689441 : ℕ)^1035*100000000000000^779 ≤ 48775698317293^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2912689441 5000000000 48775698317293 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5021476489/10000000000 : ℝ)^1035 ≤ (20021044724491/50000000000000 : ℝ)^779 := by
    have hnat : (5021476489 : ℕ)^1035*50000000000000^779 ≤ 20021044724491^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021476489 10000000000 20021044724491 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48062653/250000000 : ℝ), (2912689441/5000000000 : ℝ), (5021476489/10000000000 : ℝ)] ![(1397776526453/12500000000000 : ℝ), (48775698317293/100000000000000 : ℝ), (20021044724491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48062653/250000000 : ℝ)|^1035 ≤ (1397776526453/12500000000000 : ℝ)^779
        have hw : |(48062653/250000000 : ℝ)|=(48062653/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2912689441/5000000000 : ℝ)|^1035 ≤ (48775698317293/100000000000000 : ℝ)^779
        have hw : |(2912689441/5000000000 : ℝ)|=(2912689441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5021476489/10000000000 : ℝ)|^1035 ≤ (20021044724491/50000000000000 : ℝ)^779
        have hw : |(5021476489/10000000000 : ℝ)|=(5021476489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (667/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20691/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (37/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (37/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (37/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (37/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (37/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (37/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (37/20000 : ℝ) ^ (8279/2048 : ℝ) ≤ (896592471/100000000000000000000 : ℝ) := by
    have hpowers : (37/20000 : ℝ)^8279 ≤ (896592471/100000000000000000000 : ℝ)^2048 := by
      have hnat : (37 : ℕ)^8279*100000000000000000000^2048 ≤ 896592471^2048*20000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37 20000 896592471 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37/20000 : ℝ)) (X := (896592471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28027/100000 : ℝ) ^ (8279/2048 : ℝ) ≤ (4676589354001687/800000000000000000 : ℝ) := by
    have hpowers : (28027/100000 : ℝ)^8279 ≤ (4676589354001687/800000000000000000 : ℝ)^2048 := by
      have hnat : (28027 : ℕ)^8279*800000000000000000^2048 ≤ 4676589354001687^2048*100000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28027 100000 4676589354001687 800000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28027/100000 : ℝ)) (X := (4676589354001687/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000896592471/50000000000000000000 : ℝ) ≤ (10000000000044359/10000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50000000000896592471/50000000000000000000 : ℝ)^2048 ≤ (10000000000044359/10000000000000000 : ℝ)^8279 := by
      have hnat : (50000000000896592471 : ℕ)^2048*10000000000000000^8279 ≤ 10000000000044359^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000896592471 50000000000000000000 10000000000044359 10000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000044359/10000000000000000 : ℝ)) (X := (50000000000896592471/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50292286835073401673/50000000000000000000 : ℝ) ≤ (5007214531846143/5000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50292286835073401673/50000000000000000000 : ℝ)^2048 ≤ (5007214531846143/5000000000000000 : ℝ)^8279 := by
      have hnat : (50292286835073401673 : ℕ)^2048*5000000000000000^8279 ≤ 5007214531846143^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50292286835073401673 50000000000000000000 5007214531846143 5000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007214531846143/5000000000000000 : ℝ)) (X := (50292286835073401673/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (404676589354001687/400000000000000000 : ℝ) ≤ (10028858127340213/10000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (404676589354001687/400000000000000000 : ℝ)^2048 ≤ (10028858127340213/10000000000000000 : ℝ)^8279 := by
      have hnat : (404676589354001687 : ℕ)^2048*10000000000000000^8279 ≤ 10028858127340213^8279*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        404676589354001687 400000000000000000 10028858127340213 10000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028858127340213/10000000000000000 : ℝ)) (X := (404676589354001687/400000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(896592471/100000000000000000000 : ℝ) ≤ ((17400916327980331893/17401250000000000000 : ℝ)+2*(14429063647927/2784200000000000 : ℝ)*(37/20000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (17400916327980331893/17401250000000000000 : ℝ)+2*(14429063647927/2784200000000000 : ℝ)*(37/20000 : ℝ)=(10000000000044359/10000000000000000 : ℝ) by norm_num, show 1+2*(896592471/100000000000000000000 : ℝ)=(50000000000896592471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4676589354001687/800000000000000000 : ℝ)+(896592471/100000000000000000000 : ℝ) ≤ ((17400916327980331893/17401250000000000000 : ℝ)+(14429063647927/2784200000000000 : ℝ)*((28027/100000 : ℝ)+(37/20000 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (17400916327980331893/17401250000000000000 : ℝ)+(14429063647927/2784200000000000 : ℝ)*((28027/100000 : ℝ)+(37/20000 : ℝ))=(5007214531846143/5000000000000000 : ℝ) by norm_num, show 1+(4676589354001687/800000000000000000 : ℝ)+(896592471/100000000000000000000 : ℝ)=(50292286835073401673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4676589354001687/800000000000000000 : ℝ) ≤ ((17400916327980331893/17401250000000000000 : ℝ)+2*(14429063647927/2784200000000000 : ℝ)*(28027/100000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (17400916327980331893/17401250000000000000 : ℝ)+2*(14429063647927/2784200000000000 : ℝ)*(28027/100000 : ℝ)=(10028858127340213/10000000000000000 : ℝ) by norm_num, show 1+2*(4676589354001687/800000000000000000 : ℝ)=(404676589354001687/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17400916327980331893/17401250000000000000 : ℝ)*(X 1 0+X 2 0)+(14429063647927/2784200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (37/20000 : ℝ)) (hi := (28027/100000 : ℝ)) (c := (17400916327980331893/17401250000000000000 : ℝ)) (alpha := (14429063647927/2784200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17400916327980331893/17401250000000000000 : ℝ)*(X 0 1+X 2 1)+(14429063647927/2784200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (37/20000 : ℝ)) (hi := (28027/100000 : ℝ)) (c := (17400916327980331893/17401250000000000000 : ℝ)) (alpha := (14429063647927/2784200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17400916327980331893/17401250000000000000 : ℝ)*(X 0 2+X 1 2)+(14429063647927/2784200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (37/20000 : ℝ)) (hi := (28027/100000 : ℝ)) (c := (17400916327980331893/17401250000000000000 : ℝ)) (alpha := (14429063647927/2784200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-105898611/500000000 : ℝ)*X 0 0+(2858229637/5000000000 : ℝ)*X 0 1+(2495276677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711074813/5000000000 : ℝ)*X 1 0+(-2510828797/10000000000 : ℝ)*X 1 1+(4990553593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711075237/5000000000 : ℝ)*X 2 0+(4990552713/10000000000 : ℝ)*X 2 1+(-313853601/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322061281/10000000000 : ℝ)*X 0 0+(229163027/625000000 : ℝ)*X 0 1+(2547607473/5000000000 : ℝ)*X 0 2+(4322061281/10000000000 : ℝ)*X 1 0+(229163027/625000000 : ℝ)*X 1 1+(2547607473/5000000000 : ℝ)*X 1 2+(4322061281/10000000000 : ℝ)*X 2 0+(229163027/625000000 : ℝ)*X 2 1+(2547607473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059431041/5000000000 : ℝ)*X 0 0+(1000134827/2000000000 : ℝ)*X 0 1+(5706131781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((523656147/1000000000 : ℝ)*X 1 0+(-897623853/5000000000 : ℝ)*X 1 1+(570613411/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5236559379/10000000000 : ℝ)*X 2 0+(1141227291/2000000000 : ℝ)*X 2 1+(-112202953/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323807397/10000000000 : ℝ)*X 0 0+(5075293629/10000000000 : ℝ)*X 0 1+(921732161/2500000000 : ℝ)*X 0 2+(4323807397/10000000000 : ℝ)*X 1 0+(5075293629/10000000000 : ℝ)*X 1 1+(921732161/2500000000 : ℝ)*X 1 2+(4323807397/10000000000 : ℝ)*X 2 0+(5075293629/10000000000 : ℝ)*X 2 1+(921732161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((3960613/5000000000 : ℝ)*X 0 0+(109798901/200000000 : ℝ)*X 0 1+(6368860081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((96835561/1000000000 : ℝ)*X 1 0+(-55565889/125000000 : ℝ)*X 1 1+(277256341/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((193669739/2000000000 : ℝ)*X 2 0+(6931393357/10000000000 : ℝ)*X 2 1+(-4445292863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((48062653/250000000 : ℝ)*X 0 0+(2912689441/5000000000 : ℝ)*X 0 1+(5021476489/10000000000 : ℝ)*X 0 2+(48062653/250000000 : ℝ)*X 1 0+(2912689441/5000000000 : ℝ)*X 1 1+(5021476489/10000000000 : ℝ)*X 1 2+(48062653/250000000 : ℝ)*X 2 0+(2912689441/5000000000 : ℝ)*X 2 1+(5021476489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60465171676582094980257/5568400000000000000000000000 : ℝ) := by norm_num
    linear_combination (207757916890911/20000000000000 : ℝ)*(major0) + (207757916890911/20000000000000 : ℝ)*(major1) + (207757916890911/20000000000000 : ℝ)*(major2) + (1377591450959641/100000000000000 : ℝ)*(sp0) + (1377592148091939/100000000000000 : ℝ)*(sp1) + (34439776621169/2500000000000 : ℝ)*(sp2) + (699983460162571/100000000000000 : ℝ)*(sp3) + (1630888123/100000000000000 : ℝ)*(sp4) + (303120797/25000000000000 : ℝ)*(sp5) + (2069134447/100000000000000 : ℝ)*(sp6) + (908586001/100000000000000 : ℝ)*(sp8) + (629858639/100000000000000 : ℝ)*(sp9) + (856452559/100000000000000 : ℝ)*(sp10) + (84772411/6250000000000 : ℝ)*(sp11) + (349992408260573/50000000000000 : ℝ)*(f.failure) + (688796995216883/50000000000000 : ℝ)*(f.sum) + (4068747472293/1113680000000000000000000000 : ℝ)*base66 + (289395367338155773/348025000000000000000000000000000 : ℝ)*base67 + (390266969880780773/348025000000000000000000000000000 : ℝ)*base69 + (118845875483605773/348025000000000000000000000000000 : ℝ)*base71 + (69687028828249/27842000000000000000000000000 : ℝ)*base74 + (1797897732119319227/348025000000000000000000000000000 : ℝ)*base76 + (441337668208244227/348025000000000000000000000000000 : ℝ)*base78 + (1436903135022319227/348025000000000000000000000000000 : ℝ)*base80 + (99162089199137/27842000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (17748137/5000000000000000000000 : ℝ)*base90 + (17748137/5000000000000000000000 : ℝ)*base92 + (17748137/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6207071252901536757939859227/870062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29004037/50000000000000 : ℝ)*(lower4) + (1068896302838371/100000000000000 : ℝ)*(major0) + (1068896302838371/100000000000000 : ℝ)*(major1) + (1068896302838371/100000000000000 : ℝ)*(major2) + (231487747/20000000000000 : ℝ)*(sp0) + (1539087541/50000000000000 : ℝ)*(sp1) + (1567873573/25000000000000 : ℝ)*(sp2) + (28350308018641/2000000000000 : ℝ)*(sp4) + (1417516744054743/100000000000000 : ℝ)*(sp5) + (1417513970418531/100000000000000 : ℝ)*(sp6) + (360135102230859/50000000000000 : ℝ)*(sp7) + (3683542039/100000000000000 : ℝ)*(sp8) + (209841499/50000000000000 : ℝ)*(sp9) + (1921500459/100000000000000 : ℝ)*(sp11) + (720272125962177/100000000000000 : ℝ)*(f.failure) + (1417520241912823/100000000000000 : ℝ)*(f.sum) + (4666159552483/139210000000000000000000000000 : ℝ)*base66 + (14708384925135052447/1740125000000000000000000000000000 : ℝ)*base68 + (11239948097801552447/1740125000000000000000000000000000 : ℝ)*base70 + (2002973428142302447/1740125000000000000000000000000000 : ℝ)*base72 + (115573464660563/139210000000000000000000000000 : ℝ)*base74 + (5723434983219927447/1740125000000000000000000000000000 : ℝ)*base76 + (4075908358084177447/1740125000000000000000000000000000 : ℝ)*base78 + (2999431322238927447/1740125000000000000000000000000000 : ℝ)*base80 + (9086784100073/139210000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7328387/10000000000000000000000 : ℝ)*base89 + (7328387/10000000000000000000000 : ℝ)*base91 + (7328387/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1087_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (667/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20691/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1087_s2_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174212817/10000000000 : ℝ)*x 0 + (2760799033/5000000000 : ℝ)*x 1 + (1287427609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174212817/10000000000 : ℝ)^1035 ≤ (13168065594661/100000000000000 : ℝ)^779 := by
    have hnat : (2174212817 : ℕ)^1035*100000000000000^779 ≤ 13168065594661^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174212817 10000000000 13168065594661 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760799033/5000000000 : ℝ)^1035 ≤ (2839098604501/6250000000000 : ℝ)^779 := by
    have hnat : (2760799033 : ℕ)^1035*6250000000000^779 ≤ 2839098604501^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760799033 5000000000 2839098604501 6250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287427609/2500000000 : ℝ)^1035 ≤ (2587897295091/6250000000000 : ℝ)^779 := by
    have hnat : (1287427609 : ℕ)^1035*6250000000000^779 ≤ 2587897295091^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287427609 2500000000 2587897295091 6250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174212817/10000000000 : ℝ), (2760799033/5000000000 : ℝ), (1287427609/2500000000 : ℝ)] ![(13168065594661/100000000000000 : ℝ), (2839098604501/6250000000000 : ℝ), (2587897295091/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174212817/10000000000 : ℝ)|^1035 ≤ (13168065594661/100000000000000 : ℝ)^779
        have hw : |(-2174212817/10000000000 : ℝ)|=(2174212817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760799033/5000000000 : ℝ)|^1035 ≤ (2839098604501/6250000000000 : ℝ)^779
        have hw : |(2760799033/5000000000 : ℝ)|=(2760799033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287427609/2500000000 : ℝ)|^1035 ≤ (2587897295091/6250000000000 : ℝ)^779
        have hw : |(1287427609/2500000000 : ℝ)|=(1287427609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s2_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5376264199/10000000000 : ℝ)*x 0 + (-591996551/2500000000 : ℝ)*x 1 + (5149711009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376264199/10000000000 : ℝ)^1035 ≤ (21921961247007/50000000000000 : ℝ)^779 := by
    have hnat : (5376264199 : ℕ)^1035*50000000000000^779 ≤ 21921961247007^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376264199 10000000000 21921961247007 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591996551/2500000000 : ℝ)^1035 ≤ (28808036419/195312500000 : ℝ)^779 := by
    have hnat : (591996551 : ℕ)^1035*195312500000^779 ≤ 28808036419^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591996551 2500000000 28808036419 195312500000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149711009/10000000000 : ℝ)^1035 ≤ (5175795355341/12500000000000 : ℝ)^779 := by
    have hnat : (5149711009 : ℕ)^1035*12500000000000^779 ≤ 5175795355341^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149711009 10000000000 5175795355341 12500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376264199/10000000000 : ℝ), (-591996551/2500000000 : ℝ), (5149711009/10000000000 : ℝ)] ![(21921961247007/50000000000000 : ℝ), (28808036419/195312500000 : ℝ), (5175795355341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376264199/10000000000 : ℝ)|^1035 ≤ (21921961247007/50000000000000 : ℝ)^779
        have hw : |(5376264199/10000000000 : ℝ)|=(5376264199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-591996551/2500000000 : ℝ)|^1035 ≤ (28808036419/195312500000 : ℝ)^779
        have hw : |(-591996551/2500000000 : ℝ)|=(591996551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149711009/10000000000 : ℝ)|^1035 ≤ (5175795355341/12500000000000 : ℝ)^779
        have hw : |(5149711009/10000000000 : ℝ)|=(5149711009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s2_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5376264329/10000000000 : ℝ)*x 0 + (257485543/500000000 : ℝ)*x 1 + (-1183993113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376264329/10000000000 : ℝ)^1035 ≤ (43843923902573/100000000000000 : ℝ)^779 := by
    have hnat : (5376264329 : ℕ)^1035*100000000000000^779 ≤ 43843923902573^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376264329 10000000000 43843923902573 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257485543/500000000 : ℝ)^1035 ≤ (5175795156373/12500000000000 : ℝ)^779 := by
    have hnat : (257485543 : ℕ)^1035*12500000000000^779 ≤ 5175795156373^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257485543 500000000 5175795156373 12500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183993113/5000000000 : ℝ)^1035 ≤ (2949942965719/20000000000000 : ℝ)^779 := by
    have hnat : (1183993113 : ℕ)^1035*20000000000000^779 ≤ 2949942965719^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183993113 5000000000 2949942965719 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376264329/10000000000 : ℝ), (257485543/500000000 : ℝ), (-1183993113/5000000000 : ℝ)] ![(43843923902573/100000000000000 : ℝ), (5175795156373/12500000000000 : ℝ), (2949942965719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376264329/10000000000 : ℝ)|^1035 ≤ (43843923902573/100000000000000 : ℝ)^779
        have hw : |(5376264329/10000000000 : ℝ)|=(5376264329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257485543/500000000 : ℝ)|^1035 ≤ (5175795156373/12500000000000 : ℝ)^779
        have hw : |(257485543/500000000 : ℝ)|=(257485543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1183993113/5000000000 : ℝ)|^1035 ≤ (2949942965719/20000000000000 : ℝ)^779
        have hw : |(-1183993113/5000000000 : ℝ)|=(1183993113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s2_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2180247907/5000000000 : ℝ)*x 0 + (250622669/625000000 : ℝ)*x 1 + (592731147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180247907/5000000000 : ℝ)^1035 ≤ (16597697084167/50000000000000 : ℝ)^779 := by
    have hnat : (2180247907 : ℕ)^1035*50000000000000^779 ≤ 16597697084167^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180247907 5000000000 16597697084167 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250622669/625000000 : ℝ)^1035 ≤ (14848813637171/50000000000000 : ℝ)^779 := by
    have hnat : (250622669 : ℕ)^1035*50000000000000^779 ≤ 14848813637171^779*625000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250622669 625000000 14848813637171 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592731147/1250000000 : ℝ)^1035 ≤ (18553489271077/50000000000000 : ℝ)^779 := by
    have hnat : (592731147 : ℕ)^1035*50000000000000^779 ≤ 18553489271077^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592731147 1250000000 18553489271077 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180247907/5000000000 : ℝ), (250622669/625000000 : ℝ), (592731147/1250000000 : ℝ)] ![(16597697084167/50000000000000 : ℝ), (14848813637171/50000000000000 : ℝ), (18553489271077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180247907/5000000000 : ℝ)|^1035 ≤ (16597697084167/50000000000000 : ℝ)^779
        have hw : |(2180247907/5000000000 : ℝ)|=(2180247907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250622669/625000000 : ℝ)|^1035 ≤ (14848813637171/50000000000000 : ℝ)^779
        have hw : |(250622669/625000000 : ℝ)|=(250622669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(592731147/1250000000 : ℝ)|^1035 ≤ (18553489271077/50000000000000 : ℝ)^779
        have hw : |(592731147/1250000000 : ℝ)|=(592731147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s2_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-543582947/2500000000 : ℝ)*x 0 + (1288093941/2500000000 : ℝ)*x 1 + (1103781019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543582947/2500000000 : ℝ)^1035 ≤ (6584511469131/50000000000000 : ℝ)^779 := by
    have hnat : (543582947 : ℕ)^1035*50000000000000^779 ≤ 6584511469131^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543582947 2500000000 6584511469131 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288093941/2500000000 : ℝ)^1035 ≤ (41434832439983/100000000000000 : ℝ)^779 := by
    have hnat : (1288093941 : ℕ)^1035*100000000000000^779 ≤ 41434832439983^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288093941 2500000000 41434832439983 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103781019/2000000000 : ℝ)^1035 ≤ (11349036152779/25000000000000 : ℝ)^779 := by
    have hnat : (1103781019 : ℕ)^1035*25000000000000^779 ≤ 11349036152779^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103781019 2000000000 11349036152779 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543582947/2500000000 : ℝ), (1288093941/2500000000 : ℝ), (1103781019/2000000000 : ℝ)] ![(6584511469131/50000000000000 : ℝ), (41434832439983/100000000000000 : ℝ), (11349036152779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543582947/2500000000 : ℝ)|^1035 ≤ (6584511469131/50000000000000 : ℝ)^779
        have hw : |(-543582947/2500000000 : ℝ)|=(543582947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288093941/2500000000 : ℝ)|^1035 ≤ (41434832439983/100000000000000 : ℝ)^779
        have hw : |(1288093941/2500000000 : ℝ)|=(1288093941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103781019/2000000000 : ℝ)|^1035 ≤ (11349036152779/25000000000000 : ℝ)^779
        have hw : |(1103781019/2000000000 : ℝ)|=(1103781019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s2_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5282258337/10000000000 : ℝ)*x 0 + (-499698001/2500000000 : ℝ)*x 1 + (2759452593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282258337/10000000000 : ℝ)^1035 ≤ (10707075101151/25000000000000 : ℝ)^779 := by
    have hnat : (5282258337 : ℕ)^1035*25000000000000^779 ≤ 10707075101151^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282258337 10000000000 10707075101151 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499698001/2500000000 : ℝ)^1035 ≤ (11775553970617/100000000000000 : ℝ)^779 := by
    have hnat : (499698001 : ℕ)^1035*100000000000000^779 ≤ 11775553970617^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499698001 2500000000 11775553970617 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759452593/5000000000 : ℝ)^1035 ≤ (45396145605629/100000000000000 : ℝ)^779 := by
    have hnat : (2759452593 : ℕ)^1035*100000000000000^779 ≤ 45396145605629^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759452593 5000000000 45396145605629 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282258337/10000000000 : ℝ), (-499698001/2500000000 : ℝ), (2759452593/5000000000 : ℝ)] ![(10707075101151/25000000000000 : ℝ), (11775553970617/100000000000000 : ℝ), (45396145605629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282258337/10000000000 : ℝ)|^1035 ≤ (10707075101151/25000000000000 : ℝ)^779
        have hw : |(5282258337/10000000000 : ℝ)|=(5282258337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499698001/2500000000 : ℝ)|^1035 ≤ (11775553970617/100000000000000 : ℝ)^779
        have hw : |(-499698001/2500000000 : ℝ)|=(499698001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759452593/5000000000 : ℝ)|^1035 ≤ (45396145605629/100000000000000 : ℝ)^779
        have hw : |(2759452593/5000000000 : ℝ)|=(2759452593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s2_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2641129269/5000000000 : ℝ)*x 0 + (5518905099/10000000000 : ℝ)*x 1 + (-1998791849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641129269/5000000000 : ℝ)^1035 ≤ (8565660513973/20000000000000 : ℝ)^779 := by
    have hnat : (2641129269 : ℕ)^1035*20000000000000^779 ≤ 8565660513973^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641129269 5000000000 8565660513973 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518905099/10000000000 : ℝ)^1035 ≤ (45396144654831/100000000000000 : ℝ)^779 := by
    have hnat : (5518905099 : ℕ)^1035*100000000000000^779 ≤ 45396144654831^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518905099 10000000000 45396144654831 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1998791849/10000000000 : ℝ)^1035 ≤ (2943888189343/25000000000000 : ℝ)^779 := by
    have hnat : (1998791849 : ℕ)^1035*25000000000000^779 ≤ 2943888189343^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998791849 10000000000 2943888189343 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641129269/5000000000 : ℝ), (5518905099/10000000000 : ℝ), (-1998791849/10000000000 : ℝ)] ![(8565660513973/20000000000000 : ℝ), (45396144654831/100000000000000 : ℝ), (2943888189343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641129269/5000000000 : ℝ)|^1035 ≤ (8565660513973/20000000000000 : ℝ)^779
        have hw : |(2641129269/5000000000 : ℝ)|=(2641129269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518905099/10000000000 : ℝ)|^1035 ≤ (45396144654831/100000000000000 : ℝ)^779
        have hw : |(5518905099/10000000000 : ℝ)|=(5518905099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1998791849/10000000000 : ℝ)|^1035 ≤ (2943888189343/25000000000000 : ℝ)^779
        have hw : |(-1998791849/10000000000 : ℝ)|=(1998791849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s2_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (174429207/400000000 : ℝ)*x 0 + (947320873/2000000000 : ℝ)*x 1 + (1003815377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174429207/400000000 : ℝ)^1035 ≤ (16598882317973/50000000000000 : ℝ)^779 := by
    have hnat : (174429207 : ℕ)^1035*50000000000000^779 ≤ 16598882317973^779*400000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174429207 400000000 16598882317973 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947320873/2000000000 : ℝ)^1035 ≤ (9263114453873/25000000000000 : ℝ)^779 := by
    have hnat : (947320873 : ℕ)^1035*25000000000000^779 ≤ 9263114453873^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947320873 2000000000 9263114453873 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003815377/2500000000 : ℝ)^1035 ≤ (14874888763969/50000000000000 : ℝ)^779 := by
    have hnat : (1003815377 : ℕ)^1035*50000000000000^779 ≤ 14874888763969^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003815377 2500000000 14874888763969 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174429207/400000000 : ℝ), (947320873/2000000000 : ℝ), (1003815377/2500000000 : ℝ)] ![(16598882317973/50000000000000 : ℝ), (9263114453873/25000000000000 : ℝ), (14874888763969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174429207/400000000 : ℝ)|^1035 ≤ (16598882317973/50000000000000 : ℝ)^779
        have hw : |(174429207/400000000 : ℝ)|=(174429207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(947320873/2000000000 : ℝ)|^1035 ≤ (9263114453873/25000000000000 : ℝ)^779
        have hw : |(947320873/2000000000 : ℝ)|=(947320873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003815377/2500000000 : ℝ)|^1035 ≤ (14874888763969/50000000000000 : ℝ)^779
        have hw : |(1003815377/2500000000 : ℝ)|=(1003815377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (667/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (4407/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (521/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (667/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (667/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (667/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (667/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (667/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (667/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (667/12500 : ℝ) ^ (8279/2048 : ℝ) ≤ (715805144077769/100000000000000000000 : ℝ) := by
    have hpowers : (667/12500 : ℝ)^8279 ≤ (715805144077769/100000000000000000000 : ℝ)^2048 := by
      have hnat : (667 : ℕ)^8279*100000000000000000000^2048 ≤ 715805144077769^2048*12500^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        667 12500 715805144077769 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (667/12500 : ℝ)) (X := (715805144077769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20691/100000 : ℝ) ^ (8279/2048 : ℝ) ≤ (171419411348026717/100000000000000000000 : ℝ) := by
    have hpowers : (20691/100000 : ℝ)^8279 ≤ (171419411348026717/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20691 : ℕ)^8279*100000000000000000000^2048 ≤ 171419411348026717^2048*100000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20691 100000 171419411348026717 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20691/100000 : ℝ)) (X := (171419411348026717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000715805144077769/50000000000000000000 : ℝ) ≤ (1250004426745493/1250000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50000715805144077769/50000000000000000000 : ℝ)^2048 ≤ (1250004426745493/1250000000000000 : ℝ)^8279 := by
      have hnat : (50000715805144077769 : ℕ)^2048*1250000000000000^8279 ≤ 1250004426745493^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000715805144077769 50000000000000000000 1250004426745493 1250000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250004426745493/1250000000000000 : ℝ)) (X := (50000715805144077769/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50086067608246052243/50000000000000000000 : ℝ) ≤ (5002127701371803/5000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50086067608246052243/50000000000000000000 : ℝ)^2048 ≤ (5002127701371803/5000000000000000 : ℝ)^8279 := by
      have hnat : (50086067608246052243 : ℕ)^2048*5000000000000000^8279 ≤ 5002127701371803^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086067608246052243 50000000000000000000 5002127701371803 5000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002127701371803/5000000000000000 : ℝ)) (X := (50086067608246052243/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50171419411348026717/50000000000000000000 : ℝ) ≤ (2502118847880817/2500000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50171419411348026717/50000000000000000000 : ℝ)^2048 ≤ (2502118847880817/2500000000000000 : ℝ)^8279 := by
      have hnat : (50171419411348026717 : ℕ)^2048*2500000000000000^8279 ≤ 2502118847880817^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50171419411348026717 50000000000000000000 2502118847880817 2500000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502118847880817/2500000000000000 : ℝ)) (X := (50171419411348026717/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(715805144077769/100000000000000000000 : ℝ) ≤ ((19188188507644975907/19193750000000000000 : ℝ)+2*(2109994389831/767750000000000 : ℝ)*(667/12500 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (19188188507644975907/19193750000000000000 : ℝ)+2*(2109994389831/767750000000000 : ℝ)*(667/12500 : ℝ)=(1250004426745493/1250000000000000 : ℝ) by norm_num, show 1+2*(715805144077769/100000000000000000000 : ℝ)=(50000715805144077769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(171419411348026717/100000000000000000000 : ℝ)+(715805144077769/100000000000000000000 : ℝ) ≤ ((19188188507644975907/19193750000000000000 : ℝ)+(2109994389831/767750000000000 : ℝ)*((20691/100000 : ℝ)+(667/12500 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (19188188507644975907/19193750000000000000 : ℝ)+(2109994389831/767750000000000 : ℝ)*((20691/100000 : ℝ)+(667/12500 : ℝ))=(5002127701371803/5000000000000000 : ℝ) by norm_num, show 1+(171419411348026717/100000000000000000000 : ℝ)+(715805144077769/100000000000000000000 : ℝ)=(50086067608246052243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(171419411348026717/100000000000000000000 : ℝ) ≤ ((19188188507644975907/19193750000000000000 : ℝ)+2*(2109994389831/767750000000000 : ℝ)*(20691/100000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (19188188507644975907/19193750000000000000 : ℝ)+2*(2109994389831/767750000000000 : ℝ)*(20691/100000 : ℝ)=(2502118847880817/2500000000000000 : ℝ) by norm_num, show 1+2*(171419411348026717/100000000000000000000 : ℝ)=(50171419411348026717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19188188507644975907/19193750000000000000 : ℝ)*(X 1 0+X 2 0)+(2109994389831/767750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (667/12500 : ℝ)) (hi := (20691/100000 : ℝ)) (c := (19188188507644975907/19193750000000000000 : ℝ)) (alpha := (2109994389831/767750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19188188507644975907/19193750000000000000 : ℝ)*(X 0 1+X 2 1)+(2109994389831/767750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (667/12500 : ℝ)) (hi := (20691/100000 : ℝ)) (c := (19188188507644975907/19193750000000000000 : ℝ)) (alpha := (2109994389831/767750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19188188507644975907/19193750000000000000 : ℝ)*(X 0 2+X 1 2)+(2109994389831/767750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (667/12500 : ℝ)) (hi := (20691/100000 : ℝ)) (c := (19188188507644975907/19193750000000000000 : ℝ)) (alpha := (2109994389831/767750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2174212817/10000000000 : ℝ)*X 0 0+(2760799033/5000000000 : ℝ)*X 0 1+(1287427609/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376264199/10000000000 : ℝ)*X 1 0+(-591996551/2500000000 : ℝ)*X 1 1+(5149711009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376264329/10000000000 : ℝ)*X 2 0+(257485543/500000000 : ℝ)*X 2 1+(-1183993113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180247907/5000000000 : ℝ)*X 0 0+(250622669/625000000 : ℝ)*X 0 1+(592731147/1250000000 : ℝ)*X 0 2+(2180247907/5000000000 : ℝ)*X 1 0+(250622669/625000000 : ℝ)*X 1 1+(592731147/1250000000 : ℝ)*X 1 2+(2180247907/5000000000 : ℝ)*X 2 0+(250622669/625000000 : ℝ)*X 2 1+(592731147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-543582947/2500000000 : ℝ)*X 0 0+(1288093941/2500000000 : ℝ)*X 0 1+(1103781019/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282258337/10000000000 : ℝ)*X 1 0+(-499698001/2500000000 : ℝ)*X 1 1+(2759452593/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641129269/5000000000 : ℝ)*X 2 0+(5518905099/10000000000 : ℝ)*X 2 1+(-1998791849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174429207/400000000 : ℝ)*X 0 0+(947320873/2000000000 : ℝ)*X 0 1+(1003815377/2500000000 : ℝ)*X 0 2+(174429207/400000000 : ℝ)*X 1 0+(947320873/2000000000 : ℝ)*X 1 1+(1003815377/2500000000 : ℝ)*X 1 2+(174429207/400000000 : ℝ)*X 2 0+(947320873/2000000000 : ℝ)*X 2 1+(1003815377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1878097062131841795466239/374877929687500000000000000000 : ℝ) := by norm_num
    linear_combination (80406519/10000000000000 : ℝ)*(base19) + (433149919/50000000000000 : ℝ)*(base23) + (87414487/100000000000000 : ℝ)*(upper3) + (149811/10000000000000 : ℝ)*(upper4) + (21617401/25000000000000 : ℝ)*(upper5) + (202767550524527/10000000000000 : ℝ)*(major0) + (202767550524527/10000000000000 : ℝ)*(major1) + (202767550524527/10000000000000 : ℝ)*(major2) + (672249063702791/25000000000000 : ℝ)*(sp0) + (2689007819845837/100000000000000 : ℝ)*(sp1) + (672251939402797/25000000000000 : ℝ)*(sp2) + (1366337069469103/100000000000000 : ℝ)*(sp3) + (12369099863/100000000000000 : ℝ)*(sp4) + (1287528521/25000000000000 : ℝ)*(sp7) + (1366342219583187/100000000000000 : ℝ)*(f.failure) + (2689008623911027/100000000000000 : ℝ)*(f.sum) + (25362902766849/7677500000000000000000000000 : ℝ)*base65 + (489560235454504011/191937500000000000000000000000000 : ℝ)*base68 + (388516074656441511/191937500000000000000000000000000 : ℝ)*base70 + (154028298839941511/191937500000000000000000000000000 : ℝ)*base72 + (7554444084807/3838750000000000000000000000 : ℝ)*base73 + (1261277008726691511/191937500000000000000000000000000 : ℝ)*base76 + (1163925268627620989/191937500000000000000000000000000 : ℝ)*base77 + (402530499279754011/191937500000000000000000000000000 : ℝ)*base80 + (4171067264003/3838750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (49296697/10000000000000000000000 : ℝ)*base89 + (49296697/10000000000000000000000 : ℝ)*base91 + (49296697/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15894243348548733775203/7677500000000000000000000000 : ℝ) := by norm_num
    linear_combination (395097921/100000000000000 : ℝ)*(base19) + (22078921/4000000000000 : ℝ)*(base23) + (82377049/100000000000000 : ℝ)*(upper3) + (1860477/25000000000000 : ℝ)*(lower4) + (7392743/25000000000000 : ℝ)*(upper5) + (205729906715723/10000000000000 : ℝ)*(major0) + (205729906715723/10000000000000 : ℝ)*(major1) + (205729906715723/10000000000000 : ℝ)*(major2) + (1618356409/50000000000000 : ℝ)*(sp1) + (2713230289/50000000000000 : ℝ)*(sp2) + (1364147054811043/50000000000000 : ℝ)*(sp4) + (682072619452837/25000000000000 : ℝ)*(sp5) + (2728288131188483/100000000000000 : ℝ)*(sp6) + (173287994460559/12500000000000 : ℝ)*(sp7) + (173287994460559/12500000000000 : ℝ)*(f.failure) + (1364147054811043/50000000000000 : ℝ)*(f.sum) + (5036538821027/3838750000000000000000000000 : ℝ)*base66 + (1346220686724410761/191937500000000000000000000000000 : ℝ)*base67 + (851634121481964239/191937500000000000000000000000000 : ℝ)*base70 + (1056032532578964239/191937500000000000000000000000000 : ℝ)*base72 + (18270726681393/3838750000000000000000000000 : ℝ)*base73 + (714002634626964239/191937500000000000000000000000000 : ℝ)*base76 + (38754215544910761/191937500000000000000000000000000 : ℝ)*base77 + (474492731680473261/191937500000000000000000000000000 : ℝ)*base79 + (12517134842503/15355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8172371/1250000000000000000000 : ℝ)*base90 + (8172371/1250000000000000000000 : ℝ)*base92 + (8172371/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1087_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (667/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (521/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1087_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (521/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1087_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1087_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1087_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (521/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1087_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
