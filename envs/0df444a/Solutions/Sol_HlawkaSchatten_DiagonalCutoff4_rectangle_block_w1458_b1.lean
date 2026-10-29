-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1458_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:43.905983+00:00
-- url     : https://prove2.me/submissions/50796455-ac77-48ed-b7fe-a7a1c997dda8

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
theorem support_rectangle_w1458_s3_0 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946951403/10000000000 : ℝ)*x 0 + (338403249/625000000 : ℝ)*x 1 + (52403773/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946951403/10000000000 : ℝ)^2209 ≤ (594178905593/5000000000000 : ℝ)^1697 := by
    have hnat : (1946951403 : ℕ)^2209*5000000000000^1697 ≤ 594178905593^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946951403 10000000000 594178905593 5000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338403249/625000000 : ℝ)^2209 ≤ (44995132030261/100000000000000 : ℝ)^1697 := by
    have hnat : (338403249 : ℕ)^2209*100000000000000^1697 ≤ 44995132030261^1697*625000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338403249 625000000 44995132030261 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52403773/100000000 : ℝ)^2209 ≤ (10780322460091/25000000000000 : ℝ)^1697 := by
    have hnat : (52403773 : ℕ)^2209*25000000000000^1697 ≤ 10780322460091^1697*100000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52403773 100000000 10780322460091 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946951403/10000000000 : ℝ), (338403249/625000000 : ℝ), (52403773/100000000 : ℝ)] ![(594178905593/5000000000000 : ℝ), (44995132030261/100000000000000 : ℝ), (10780322460091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946951403/10000000000 : ℝ)|^2209 ≤ (594178905593/5000000000000 : ℝ)^1697
        have hw : |(-1946951403/10000000000 : ℝ)|=(1946951403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338403249/625000000 : ℝ)|^2209 ≤ (44995132030261/100000000000000 : ℝ)^1697
        have hw : |(338403249/625000000 : ℝ)|=(338403249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52403773/100000000 : ℝ)|^2209 ≤ (10780322460091/25000000000000 : ℝ)^1697
        have hw : |(52403773/100000000 : ℝ)|=(52403773/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s3_1 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069740733/2000000000 : ℝ)*x 0 + (-2035699651/10000000000 : ℝ)*x 1 + (5240377289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069740733/2000000000 : ℝ)^2209 ≤ (276782558983/625000000000 : ℝ)^1697 := by
    have hnat : (1069740733 : ℕ)^2209*625000000000^1697 ≤ 276782558983^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069740733 2000000000 276782558983 625000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2035699651/10000000000 : ℝ)^2209 ≤ (1574187603389/12500000000000 : ℝ)^1697 := by
    have hnat : (2035699651 : ℕ)^2209*12500000000000^1697 ≤ 1574187603389^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035699651 10000000000 1574187603389 12500000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240377289/10000000000 : ℝ)^2209 ≤ (43121289722539/100000000000000 : ℝ)^1697 := by
    have hnat : (5240377289 : ℕ)^2209*100000000000000^1697 ≤ 43121289722539^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240377289 10000000000 43121289722539 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069740733/2000000000 : ℝ), (-2035699651/10000000000 : ℝ), (5240377289/10000000000 : ℝ)] ![(276782558983/625000000000 : ℝ), (1574187603389/12500000000000 : ℝ), (43121289722539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069740733/2000000000 : ℝ)|^2209 ≤ (276782558983/625000000000 : ℝ)^1697
        have hw : |(1069740733/2000000000 : ℝ)|=(1069740733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2035699651/10000000000 : ℝ)|^2209 ≤ (1574187603389/12500000000000 : ℝ)^1697
        have hw : |(-2035699651/10000000000 : ℝ)|=(2035699651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240377289/10000000000 : ℝ)|^2209 ≤ (43121289722539/100000000000000 : ℝ)^1697
        have hw : |(5240377289/10000000000 : ℝ)|=(5240377289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s3_2 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668587797/1250000000 : ℝ)*x 0 + (5240377889/10000000000 : ℝ)*x 1 + (-2035700579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668587797/1250000000 : ℝ)^2209 ≤ (4428519554489/10000000000000 : ℝ)^1697 := by
    have hnat : (668587797 : ℕ)^2209*10000000000000^1697 ≤ 4428519554489^1697*1250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668587797 1250000000 4428519554489 10000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240377889/10000000000 : ℝ)^2209 ≤ (10780324037333/25000000000000 : ℝ)^1697 := by
    have hnat : (5240377889 : ℕ)^2209*25000000000000^1697 ≤ 10780324037333^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240377889 10000000000 10780324037333 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035700579/10000000000 : ℝ)^2209 ≤ (12593508300107/100000000000000 : ℝ)^1697 := by
    have hnat : (2035700579 : ℕ)^2209*100000000000000^1697 ≤ 12593508300107^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035700579 10000000000 12593508300107 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668587797/1250000000 : ℝ), (5240377889/10000000000 : ℝ), (-2035700579/10000000000 : ℝ)] ![(4428519554489/10000000000000 : ℝ), (10780324037333/25000000000000 : ℝ), (12593508300107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668587797/1250000000 : ℝ)|^2209 ≤ (4428519554489/10000000000000 : ℝ)^1697
        have hw : |(668587797/1250000000 : ℝ)|=(668587797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240377889/10000000000 : ℝ)|^2209 ≤ (10780324037333/25000000000000 : ℝ)^1697
        have hw : |(5240377889/10000000000 : ℝ)|=(5240377889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035700579/10000000000 : ℝ)|^2209 ≤ (12593508300107/100000000000000 : ℝ)^1697
        have hw : |(-2035700579/10000000000 : ℝ)|=(2035700579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s3_3 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074157051/2500000000 : ℝ)*x 0 + (513759823/1250000000 : ℝ)*x 1 + (4490663133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074157051/2500000000 : ℝ)^2209 ≤ (8324902749629/25000000000000 : ℝ)^1697 := by
    have hnat : (1074157051 : ℕ)^2209*25000000000000^1697 ≤ 8324902749629^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074157051 2500000000 8324902749629 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513759823/1250000000 : ℝ)^2209 ≤ (6286012903371/20000000000000 : ℝ)^1697 := by
    have hnat : (513759823 : ℕ)^2209*20000000000000^1697 ≤ 6286012903371^1697*1250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513759823 1250000000 6286012903371 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490663133/10000000000 : ℝ)^2209 ≤ (7054064895083/20000000000000 : ℝ)^1697 := by
    have hnat : (4490663133 : ℕ)^2209*20000000000000^1697 ≤ 7054064895083^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490663133 10000000000 7054064895083 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074157051/2500000000 : ℝ), (513759823/1250000000 : ℝ), (4490663133/10000000000 : ℝ)] ![(8324902749629/25000000000000 : ℝ), (6286012903371/20000000000000 : ℝ), (7054064895083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074157051/2500000000 : ℝ)|^2209 ≤ (8324902749629/25000000000000 : ℝ)^1697
        have hw : |(1074157051/2500000000 : ℝ)|=(1074157051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513759823/1250000000 : ℝ)|^2209 ≤ (6286012903371/20000000000000 : ℝ)^1697
        have hw : |(513759823/1250000000 : ℝ)|=(513759823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490663133/10000000000 : ℝ)|^2209 ≤ (7054064895083/20000000000000 : ℝ)^1697
        have hw : |(4490663133/10000000000 : ℝ)|=(4490663133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s3_4 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-973482809/5000000000 : ℝ)*x 0 + (327566603/625000000 : ℝ)*x 1 + (5413759923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973482809/5000000000 : ℝ)^2209 ≤ (11883691053303/100000000000000 : ℝ)^1697 := by
    have hnat : (973482809 : ℕ)^2209*100000000000000^1697 ≤ 11883691053303^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973482809 5000000000 11883691053303 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327566603/625000000 : ℝ)^2209 ≤ (43128663103277/100000000000000 : ℝ)^1697 := by
    have hnat : (327566603 : ℕ)^2209*100000000000000^1697 ≤ 43128663103277^1697*625000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327566603 625000000 43128663103277 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413759923/10000000000 : ℝ)^2209 ≤ (5623455729917/12500000000000 : ℝ)^1697 := by
    have hnat : (5413759923 : ℕ)^2209*12500000000000^1697 ≤ 5623455729917^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413759923 10000000000 5623455729917 12500000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-973482809/5000000000 : ℝ), (327566603/625000000 : ℝ), (5413759923/10000000000 : ℝ)] ![(11883691053303/100000000000000 : ℝ), (43128663103277/100000000000000 : ℝ), (5623455729917/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-973482809/5000000000 : ℝ)|^2209 ≤ (11883691053303/100000000000000 : ℝ)^1697
        have hw : |(-973482809/5000000000 : ℝ)|=(973482809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327566603/625000000 : ℝ)|^2209 ≤ (43128663103277/100000000000000 : ℝ)^1697
        have hw : |(327566603/625000000 : ℝ)|=(327566603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413759923/10000000000 : ℝ)|^2209 ≤ (5623455729917/12500000000000 : ℝ)^1697
        have hw : |(5413759923/10000000000 : ℝ)|=(5413759923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s3_5 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325831037/2500000000 : ℝ)*x 0 + (-931159013/5000000000 : ℝ)*x 1 + (1082751981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325831037/2500000000 : ℝ)^2209 ≤ (1368648504303/3125000000000 : ℝ)^1697 := by
    have hnat : (1325831037 : ℕ)^2209*3125000000000^1697 ≤ 1368648504303^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325831037 2500000000 1368648504303 3125000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (931159013/5000000000 : ℝ)^2209 ≤ (5607801104571/50000000000000 : ℝ)^1697 := by
    have hnat : (931159013 : ℕ)^2209*50000000000000^1697 ≤ 5607801104571^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931159013 5000000000 5607801104571 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082751981/2000000000 : ℝ)^2209 ≤ (4498764564463/10000000000000 : ℝ)^1697 := by
    have hnat : (1082751981 : ℕ)^2209*10000000000000^1697 ≤ 4498764564463^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082751981 2000000000 4498764564463 10000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325831037/2500000000 : ℝ), (-931159013/5000000000 : ℝ), (1082751981/2000000000 : ℝ)] ![(1368648504303/3125000000000 : ℝ), (5607801104571/50000000000000 : ℝ), (4498764564463/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325831037/2500000000 : ℝ)|^2209 ≤ (1368648504303/3125000000000 : ℝ)^1697
        have hw : |(1325831037/2500000000 : ℝ)|=(1325831037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-931159013/5000000000 : ℝ)|^2209 ≤ (5607801104571/50000000000000 : ℝ)^1697
        have hw : |(-931159013/5000000000 : ℝ)|=(931159013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082751981/2000000000 : ℝ)|^2209 ≤ (4498764564463/10000000000000 : ℝ)^1697
        have hw : |(1082751981/2000000000 : ℝ)|=(1082751981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s3_6 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325830777/2500000000 : ℝ)*x 0 + (5413760709/10000000000 : ℝ)*x 1 + (-931159171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325830777/2500000000 : ℝ)^2209 ≤ (21898370478859/50000000000000 : ℝ)^1697 := by
    have hnat : (1325830777 : ℕ)^2209*50000000000000^1697 ≤ 21898370478859^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325830777 2500000000 21898370478859 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413760709/10000000000 : ℝ)^2209 ≤ (11246913585381/25000000000000 : ℝ)^1697 := by
    have hnat : (5413760709 : ℕ)^2209*25000000000000^1697 ≤ 11246913585381^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413760709 10000000000 11246913585381 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931159171/5000000000 : ℝ)^2209 ≤ (11215604686391/100000000000000 : ℝ)^1697 := by
    have hnat : (931159171 : ℕ)^2209*100000000000000^1697 ≤ 11215604686391^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931159171 5000000000 11215604686391 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325830777/2500000000 : ℝ), (5413760709/10000000000 : ℝ), (-931159171/5000000000 : ℝ)] ![(21898370478859/50000000000000 : ℝ), (11246913585381/25000000000000 : ℝ), (11215604686391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325830777/2500000000 : ℝ)|^2209 ≤ (21898370478859/50000000000000 : ℝ)^1697
        have hw : |(1325830777/2500000000 : ℝ)|=(1325830777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413760709/10000000000 : ℝ)|^2209 ≤ (11246913585381/25000000000000 : ℝ)^1697
        have hw : |(5413760709/10000000000 : ℝ)|=(5413760709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931159171/5000000000 : ℝ)|^2209 ≤ (11215604686391/100000000000000 : ℝ)^1697
        have hw : |(-931159171/5000000000 : ℝ)|=(931159171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s3_7 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67135303/156250000 : ℝ)*x 0 + (2244579841/5000000000 : ℝ)*x 1 + (64243609/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67135303/156250000 : ℝ)^2209 ≤ (8324981409507/25000000000000 : ℝ)^1697 := by
    have hnat : (67135303 : ℕ)^2209*25000000000000^1697 ≤ 8324981409507^1697*156250000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67135303 156250000 8324981409507 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244579841/5000000000 : ℝ)^2209 ≤ (17627477125779/50000000000000 : ℝ)^1697 := by
    have hnat : (2244579841 : ℕ)^2209*50000000000000^1697 ≤ 17627477125779^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244579841 5000000000 17627477125779 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64243609/156250000 : ℝ)^2209 ≤ (31445120097063/100000000000000 : ℝ)^1697 := by
    have hnat : (64243609 : ℕ)^2209*100000000000000^1697 ≤ 31445120097063^1697*156250000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64243609 156250000 31445120097063 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67135303/156250000 : ℝ), (2244579841/5000000000 : ℝ), (64243609/156250000 : ℝ)] ![(8324981409507/25000000000000 : ℝ), (17627477125779/50000000000000 : ℝ), (31445120097063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67135303/156250000 : ℝ)|^2209 ≤ (8324981409507/25000000000000 : ℝ)^1697
        have hw : |(67135303/156250000 : ℝ)|=(67135303/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244579841/5000000000 : ℝ)|^2209 ≤ (17627477125779/50000000000000 : ℝ)^1697
        have hw : |(2244579841/5000000000 : ℝ)|=(2244579841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64243609/156250000 : ℝ)|^2209 ≤ (31445120097063/100000000000000 : ℝ)^1697
        have hw : |(64243609/156250000 : ℝ)|=(64243609/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1458_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7857/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14933/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7857/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10517/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7857/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10517/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7857/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10517/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7857/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10517/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7857/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10517/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7857/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10517/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10517/100000 : ℝ) ^ (4417/1024 : ℝ) ≤ (6038839993019923/100000000000000000000 : ℝ) := by
    have hpowers : (10517/100000 : ℝ)^4417 ≤ (6038839993019923/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10517 : ℕ)^4417*100000000000000000000^1024 ≤ 6038839993019923^1024*100000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10517 100000 6038839993019923 100000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10517/100000 : ℝ)) (X := (6038839993019923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7857/50000 : ℝ) ^ (4417/1024 : ℝ) ≤ (34135143115146631/100000000000000000000 : ℝ) := by
    have hpowers : (7857/50000 : ℝ)^4417 ≤ (34135143115146631/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7857 : ℕ)^4417*100000000000000000000^1024 ≤ 34135143115146631^1024*50000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7857 50000 34135143115146631 100000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7857/50000 : ℝ)) (X := (34135143115146631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006038839993019923/50000000000000000000 : ℝ) ≤ (5000139992875653/5000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50006038839993019923/50000000000000000000 : ℝ)^1024 ≤ (5000139992875653/5000000000000000 : ℝ)^4417 := by
      have hnat : (50006038839993019923 : ℕ)^1024*5000000000000000^4417 ≤ 5000139992875653^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006038839993019923 50000000000000000000 5000139992875653 5000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139992875653/5000000000000000 : ℝ)) (X := (50006038839993019923/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020086991554083277/50000000000000000000 : ℝ) ≤ (5000465608020241/5000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50020086991554083277/50000000000000000000 : ℝ)^1024 ≤ (5000465608020241/5000000000000000 : ℝ)^4417 := by
      have hnat : (50020086991554083277 : ℕ)^1024*5000000000000000^4417 ≤ 5000465608020241^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020086991554083277 50000000000000000000 5000465608020241 5000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000465608020241/5000000000000000 : ℝ)) (X := (50020086991554083277/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034135143115146631/50000000000000000000 : ℝ) ≤ (5000791223164829/5000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50034135143115146631/50000000000000000000 : ℝ)^1024 ≤ (5000791223164829/5000000000000000 : ℝ)^4417 := by
      have hnat : (50034135143115146631 : ℕ)^1024*5000000000000000^4417 ≤ 5000791223164829^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034135143115146631 50000000000000000000 5000791223164829 5000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000791223164829/5000000000000000 : ℝ)) (X := (50034135143115146631/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6038839993019923/100000000000000000000 : ℝ) ≤ ((25978878554023504649/25985000000000000000 : ℝ)+2*(81403786147/64962500000000 : ℝ)*(10517/100000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (25978878554023504649/25985000000000000000 : ℝ)+2*(81403786147/64962500000000 : ℝ)*(10517/100000 : ℝ)=(5000139992875653/5000000000000000 : ℝ) by norm_num, show 1+2*(6038839993019923/100000000000000000000 : ℝ)=(50006038839993019923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34135143115146631/100000000000000000000 : ℝ)+(6038839993019923/100000000000000000000 : ℝ) ≤ ((25978878554023504649/25985000000000000000 : ℝ)+(81403786147/64962500000000 : ℝ)*((7857/50000 : ℝ)+(10517/100000 : ℝ)))^(4417/1024 : ℝ) := by
    rw [show (25978878554023504649/25985000000000000000 : ℝ)+(81403786147/64962500000000 : ℝ)*((7857/50000 : ℝ)+(10517/100000 : ℝ))=(5000465608020241/5000000000000000 : ℝ) by norm_num, show 1+(34135143115146631/100000000000000000000 : ℝ)+(6038839993019923/100000000000000000000 : ℝ)=(50020086991554083277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34135143115146631/100000000000000000000 : ℝ) ≤ ((25978878554023504649/25985000000000000000 : ℝ)+2*(81403786147/64962500000000 : ℝ)*(7857/50000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (25978878554023504649/25985000000000000000 : ℝ)+2*(81403786147/64962500000000 : ℝ)*(7857/50000 : ℝ)=(5000791223164829/5000000000000000 : ℝ) by norm_num, show 1+2*(34135143115146631/100000000000000000000 : ℝ)=(50034135143115146631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25978878554023504649/25985000000000000000 : ℝ)*(X 1 0+X 2 0)+(81403786147/64962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (10517/100000 : ℝ)) (hi := (7857/50000 : ℝ)) (c := (25978878554023504649/25985000000000000000 : ℝ)) (alpha := (81403786147/64962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25978878554023504649/25985000000000000000 : ℝ)*(X 0 1+X 2 1)+(81403786147/64962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (10517/100000 : ℝ)) (hi := (7857/50000 : ℝ)) (c := (25978878554023504649/25985000000000000000 : ℝ)) (alpha := (81403786147/64962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25978878554023504649/25985000000000000000 : ℝ)*(X 0 2+X 1 2)+(81403786147/64962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (10517/100000 : ℝ)) (hi := (7857/50000 : ℝ)) (c := (25978878554023504649/25985000000000000000 : ℝ)) (alpha := (81403786147/64962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1946951403/10000000000 : ℝ)*X 0 0+(338403249/625000000 : ℝ)*X 0 1+(52403773/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069740733/2000000000 : ℝ)*X 1 0+(-2035699651/10000000000 : ℝ)*X 1 1+(5240377289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668587797/1250000000 : ℝ)*X 2 0+(5240377889/10000000000 : ℝ)*X 2 1+(-2035700579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074157051/2500000000 : ℝ)*X 0 0+(513759823/1250000000 : ℝ)*X 0 1+(4490663133/10000000000 : ℝ)*X 0 2+(1074157051/2500000000 : ℝ)*X 1 0+(513759823/1250000000 : ℝ)*X 1 1+(4490663133/10000000000 : ℝ)*X 1 2+(1074157051/2500000000 : ℝ)*X 2 0+(513759823/1250000000 : ℝ)*X 2 1+(4490663133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-973482809/5000000000 : ℝ)*X 0 0+(327566603/625000000 : ℝ)*X 0 1+(5413759923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325831037/2500000000 : ℝ)*X 1 0+(-931159013/5000000000 : ℝ)*X 1 1+(1082751981/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325830777/2500000000 : ℝ)*X 2 0+(5413760709/10000000000 : ℝ)*X 2 1+(-931159171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((67135303/156250000 : ℝ)*X 0 0+(2244579841/5000000000 : ℝ)*X 0 1+(64243609/156250000 : ℝ)*X 0 2+(67135303/156250000 : ℝ)*X 1 0+(2244579841/5000000000 : ℝ)*X 1 1+(64243609/156250000 : ℝ)*X 1 2+(67135303/156250000 : ℝ)*X 2 0+(2244579841/5000000000 : ℝ)*X 2 1+(64243609/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187335486608652660418043079/51970000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (134056477/25000000000000 : ℝ)*(base19) + (63952471/25000000000000 : ℝ)*(upper2) + (54775557/20000000000000 : ℝ)*(lower4) + (22918759/50000000000000 : ℝ)*(lower5) + (167445208792357/4000000000000 : ℝ)*(major0) + (167445208792357/4000000000000 : ℝ)*(major1) + (167445208792357/4000000000000 : ℝ)*(major2) + (5744699419395437/100000000000000 : ℝ)*(sp0) + (718089154867521/12500000000000 : ℝ)*(sp1) + (2872348513118879/50000000000000 : ℝ)*(sp2) + (656886452671069/25000000000000 : ℝ)*(sp3) + (14355770639/100000000000000 : ℝ)*(sp4) + (8374464159/50000000000000 : ℝ)*(sp6) + (18340283/2500000000000 : ℝ)*(sp7) + (525509308859119/20000000000000 : ℝ)*(f.failure) + (1436178443791519/25000000000000 : ℝ)*(f.sum) + (101076523662847/5197000000000000000000000000 : ℝ)*base66 + (419616656131007693/103940000000000000000000000000000 : ℝ)*base67 + (832629017187732307/103940000000000000000000000000000 : ℝ)*base70 + (850561529591392307/103940000000000000000000000000000 : ℝ)*base72 + (72410408437/20300781250000000000000000 : ℝ)*base74 + (223363584511567693/103940000000000000000000000000000 : ℝ)*base75 + (1509870581141472307/103940000000000000000000000000000 : ℝ)*base78 + (323646252190352307/103940000000000000000000000000000 : ℝ)*base80 + (1731114596567/519700000000000000000000000 : ℝ)*base82 + (26277/125000000000000000000 : ℝ)*base90 + (26277/125000000000000000000 : ℝ)*base92 + (26277/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11879568654582517924449285831/1299250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2665759/4000000000000 : ℝ)*(base8) + (622886953/100000000000000 : ℝ)*(base21) + (138786959/100000000000000 : ℝ)*(upper2) + (168018881/100000000000000 : ℝ)*(lower4) + (4219548530440827/100000000000000 : ℝ)*(major0) + (4219548530440827/100000000000000 : ℝ)*(major1) + (4219548530440827/100000000000000 : ℝ)*(major2) + (4199361/800000000000 : ℝ)*(sp0) + (2004677147/100000000000000 : ℝ)*(sp1) + (1317906981/50000000000000 : ℝ)*(sp2) + (5790573644338907/100000000000000 : ℝ)*(sp4) + (289528611561293/5000000000000 : ℝ)*(sp5) + (5790570977202093/100000000000000 : ℝ)*(sp6) + (33106531502481/1250000000000 : ℝ)*(sp7) + (33106531502481/1250000000000 : ℝ)*(f.failure) + (5790574235903007/100000000000000 : ℝ)*(f.sum) + (876192818056563/25985000000000000000000000000 : ℝ)*base66 + (2375670557425504723/2598500000000000000000000000000000 : ℝ)*base67 + (12568091802993004723/2598500000000000000000000000000000 : ℝ)*base69 + (7571612710674004723/2598500000000000000000000000000000 : ℝ)*base71 + (10554929959903/25985000000000000000000000000 : ℝ)*base74 + (96662307523995277/2598500000000000000000000000000000 : ℝ)*base76 + (44066173927655504723/2598500000000000000000000000000000 : ℝ)*base77 + (9117249173845995277/2598500000000000000000000000000000 : ℝ)*base80 + (7107023788173/6496250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2949/3906250000000000000 : ℝ)*base90 + (2949/3906250000000000000 : ℝ)*base92 + (2949/3906250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1458_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7857/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1458_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1458_s4_0 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947715269/10000000000 : ℝ)*x 0 + (5407837443/10000000000 : ℝ)*x 1 + (2623244217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947715269/10000000000 : ℝ)^2209 ≤ (2377929511059/20000000000000 : ℝ)^1697 := by
    have hnat : (1947715269 : ℕ)^2209*20000000000000^1697 ≤ 2377929511059^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947715269 10000000000 2377929511059 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407837443/10000000000 : ℝ)^2209 ≤ (44923592753779/100000000000000 : ℝ)^1697 := by
    have hnat : (5407837443 : ℕ)^2209*100000000000000^1697 ≤ 44923592753779^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407837443 10000000000 44923592753779 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623244217/5000000000 : ℝ)^2209 ≤ (21593379837237/50000000000000 : ℝ)^1697 := by
    have hnat : (2623244217 : ℕ)^2209*50000000000000^1697 ≤ 21593379837237^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623244217 5000000000 21593379837237 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947715269/10000000000 : ℝ), (5407837443/10000000000 : ℝ), (2623244217/5000000000 : ℝ)] ![(2377929511059/20000000000000 : ℝ), (44923592753779/100000000000000 : ℝ), (21593379837237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947715269/10000000000 : ℝ)|^2209 ≤ (2377929511059/20000000000000 : ℝ)^1697
        have hw : |(-1947715269/10000000000 : ℝ)|=(1947715269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407837443/10000000000 : ℝ)|^2209 ≤ (44923592753779/100000000000000 : ℝ)^1697
        have hw : |(5407837443/10000000000 : ℝ)|=(5407837443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623244217/5000000000 : ℝ)|^2209 ≤ (21593379837237/50000000000000 : ℝ)^1697
        have hw : |(2623244217/5000000000 : ℝ)|=(2623244217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s4_1 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336747463/2500000000 : ℝ)*x 0 + (-2029860453/10000000000 : ℝ)*x 1 + (5246488577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336747463/2500000000 : ℝ)^2209 ≤ (44266739455043/100000000000000 : ℝ)^1697 := by
    have hnat : (1336747463 : ℕ)^2209*100000000000000^1697 ≤ 44266739455043^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336747463 2500000000 44266739455043 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2029860453/10000000000 : ℝ)^2209 ≤ (6273249661397/50000000000000 : ℝ)^1697 := by
    have hnat : (2029860453 : ℕ)^2209*50000000000000^1697 ≤ 6273249661397^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029860453 10000000000 6273249661397 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246488577/10000000000 : ℝ)^2209 ≤ (43186761206731/100000000000000 : ℝ)^1697 := by
    have hnat : (5246488577 : ℕ)^2209*100000000000000^1697 ≤ 43186761206731^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246488577 10000000000 43186761206731 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336747463/2500000000 : ℝ), (-2029860453/10000000000 : ℝ), (5246488577/10000000000 : ℝ)] ![(44266739455043/100000000000000 : ℝ), (6273249661397/50000000000000 : ℝ), (43186761206731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336747463/2500000000 : ℝ)|^2209 ≤ (44266739455043/100000000000000 : ℝ)^1697
        have hw : |(1336747463/2500000000 : ℝ)|=(1336747463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2029860453/10000000000 : ℝ)|^2209 ≤ (6273249661397/50000000000000 : ℝ)^1697
        have hw : |(-2029860453/10000000000 : ℝ)|=(2029860453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246488577/10000000000 : ℝ)|^2209 ≤ (43186761206731/100000000000000 : ℝ)^1697
        have hw : |(5246488577/10000000000 : ℝ)|=(5246488577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s4_2 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267349483/500000000 : ℝ)*x 0 + (5246488761/10000000000 : ℝ)*x 1 + (-405972093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267349483/500000000 : ℝ)^2209 ≤ (22133368692967/50000000000000 : ℝ)^1697 := by
    have hnat : (267349483 : ℕ)^2209*50000000000000^1697 ≤ 22133368692967^1697*500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267349483 500000000 22133368692967 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246488761/10000000000 : ℝ)^2209 ≤ (10796690794577/25000000000000 : ℝ)^1697 := by
    have hnat : (5246488761 : ℕ)^2209*25000000000000^1697 ≤ 10796690794577^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246488761 10000000000 10796690794577 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405972093/2000000000 : ℝ)^2209 ≤ (784156213709/6250000000000 : ℝ)^1697 := by
    have hnat : (405972093 : ℕ)^2209*6250000000000^1697 ≤ 784156213709^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405972093 2000000000 784156213709 6250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267349483/500000000 : ℝ), (5246488761/10000000000 : ℝ), (-405972093/2000000000 : ℝ)] ![(22133368692967/50000000000000 : ℝ), (10796690794577/25000000000000 : ℝ), (784156213709/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267349483/500000000 : ℝ)|^2209 ≤ (22133368692967/50000000000000 : ℝ)^1697
        have hw : |(267349483/500000000 : ℝ)|=(267349483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246488761/10000000000 : ℝ)|^2209 ≤ (10796690794577/25000000000000 : ℝ)^1697
        have hw : |(5246488761/10000000000 : ℝ)|=(5246488761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405972093/2000000000 : ℝ)|^2209 ≤ (784156213709/6250000000000 : ℝ)^1697
        have hw : |(-405972093/2000000000 : ℝ)|=(405972093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s4_3 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2148549411/5000000000 : ℝ)*x 0 + (1030983211/2500000000 : ℝ)*x 1 + (4476696333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148549411/5000000000 : ℝ)^2209 ≤ (33304358892013/100000000000000 : ℝ)^1697 := by
    have hnat : (2148549411 : ℕ)^2209*100000000000000^1697 ≤ 33304358892013^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148549411 5000000000 33304358892013 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030983211/2500000000 : ℝ)^2209 ≤ (15784021753811/50000000000000 : ℝ)^1697 := by
    have hnat : (1030983211 : ℕ)^2209*50000000000000^1697 ≤ 15784021753811^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030983211 2500000000 15784021753811 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476696333/10000000000 : ℝ)^2209 ≤ (35127597584687/100000000000000 : ℝ)^1697 := by
    have hnat : (4476696333 : ℕ)^2209*100000000000000^1697 ≤ 35127597584687^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476696333 10000000000 35127597584687 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148549411/5000000000 : ℝ), (1030983211/2500000000 : ℝ), (4476696333/10000000000 : ℝ)] ![(33304358892013/100000000000000 : ℝ), (15784021753811/50000000000000 : ℝ), (35127597584687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148549411/5000000000 : ℝ)|^2209 ≤ (33304358892013/100000000000000 : ℝ)^1697
        have hw : |(2148549411/5000000000 : ℝ)|=(2148549411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030983211/2500000000 : ℝ)|^2209 ≤ (15784021753811/50000000000000 : ℝ)^1697
        have hw : |(1030983211/2500000000 : ℝ)|=(1030983211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476696333/10000000000 : ℝ)|^2209 ≤ (35127597584687/100000000000000 : ℝ)^1697
        have hw : |(4476696333/10000000000 : ℝ)|=(4476696333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s4_4 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-486931747/2500000000 : ℝ)*x 0 + (209883191/400000000 : ℝ)*x 1 + (5407242851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486931747/2500000000 : ℝ)^2209 ≤ (2377948135289/20000000000000 : ℝ)^1697 := by
    have hnat : (486931747 : ℕ)^2209*20000000000000^1697 ≤ 2377948135289^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486931747 2500000000 2377948135289 20000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209883191/400000000 : ℝ)^2209 ≤ (539913700669/1250000000000 : ℝ)^1697 := by
    have hnat : (209883191 : ℕ)^2209*1250000000000^1697 ≤ 539913700669^1697*400000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209883191 400000000 539913700669 1250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407242851/10000000000 : ℝ)^2209 ≤ (22458581631449/50000000000000 : ℝ)^1697 := by
    have hnat : (5407242851 : ℕ)^2209*50000000000000^1697 ≤ 22458581631449^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407242851 10000000000 22458581631449 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486931747/2500000000 : ℝ), (209883191/400000000 : ℝ), (5407242851/10000000000 : ℝ)] ![(2377948135289/20000000000000 : ℝ), (539913700669/1250000000000 : ℝ), (22458581631449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486931747/2500000000 : ℝ)|^2209 ≤ (2377948135289/20000000000000 : ℝ)^1697
        have hw : |(-486931747/2500000000 : ℝ)|=(486931747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209883191/400000000 : ℝ)|^2209 ≤ (539913700669/1250000000000 : ℝ)^1697
        have hw : |(209883191/400000000 : ℝ)|=(209883191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407242851/10000000000 : ℝ)|^2209 ≤ (22458581631449/50000000000000 : ℝ)^1697
        have hw : |(5407242851/10000000000 : ℝ)|=(5407242851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s4_5 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652463799/5000000000 : ℝ)*x 0 + (-93455311/500000000 : ℝ)*x 1 + (5407242847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652463799/5000000000 : ℝ)^2209 ≤ (43813989977279/100000000000000 : ℝ)^1697 := by
    have hnat : (2652463799 : ℕ)^2209*100000000000000^1697 ≤ 43813989977279^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652463799 5000000000 43813989977279 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93455311/500000000 : ℝ)^2209 ≤ (88037865541/781250000000 : ℝ)^1697 := by
    have hnat : (93455311 : ℕ)^2209*781250000000^1697 ≤ 88037865541^1697*500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93455311 500000000 88037865541 781250000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407242847/10000000000 : ℝ)^2209 ≤ (22458581609823/50000000000000 : ℝ)^1697 := by
    have hnat : (5407242847 : ℕ)^2209*50000000000000^1697 ≤ 22458581609823^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407242847 10000000000 22458581609823 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652463799/5000000000 : ℝ), (-93455311/500000000 : ℝ), (5407242847/10000000000 : ℝ)] ![(43813989977279/100000000000000 : ℝ), (88037865541/781250000000 : ℝ), (22458581609823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652463799/5000000000 : ℝ)|^2209 ≤ (43813989977279/100000000000000 : ℝ)^1697
        have hw : |(2652463799/5000000000 : ℝ)|=(2652463799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93455311/500000000 : ℝ)|^2209 ≤ (88037865541/781250000000 : ℝ)^1697
        have hw : |(-93455311/500000000 : ℝ)|=(93455311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407242847/10000000000 : ℝ)|^2209 ≤ (22458581609823/50000000000000 : ℝ)^1697
        have hw : |(5407242847/10000000000 : ℝ)|=(5407242847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s4_6 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663115953/1250000000 : ℝ)*x 0 + (5407242831/10000000000 : ℝ)*x 1 + (-934553103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663115953/1250000000 : ℝ)^2209 ≤ (10953497564201/25000000000000 : ℝ)^1697 := by
    have hnat : (663115953 : ℕ)^2209*25000000000000^1697 ≤ 10953497564201^1697*1250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663115953 1250000000 10953497564201 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407242831/10000000000 : ℝ)^2209 ≤ (11229290761659/25000000000000 : ℝ)^1697 := by
    have hnat : (5407242831 : ℕ)^2209*25000000000000^1697 ≤ 11229290761659^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407242831 10000000000 11229290761659 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934553103/5000000000 : ℝ)^2209 ≤ (704302917461/6250000000000 : ℝ)^1697 := by
    have hnat : (934553103 : ℕ)^2209*6250000000000^1697 ≤ 704302917461^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934553103 5000000000 704302917461 6250000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663115953/1250000000 : ℝ), (5407242831/10000000000 : ℝ), (-934553103/5000000000 : ℝ)] ![(10953497564201/25000000000000 : ℝ), (11229290761659/25000000000000 : ℝ), (704302917461/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663115953/1250000000 : ℝ)|^2209 ≤ (10953497564201/25000000000000 : ℝ)^1697
        have hw : |(663115953/1250000000 : ℝ)|=(663115953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407242831/10000000000 : ℝ)|^2209 ≤ (11229290761659/25000000000000 : ℝ)^1697
        have hw : |(5407242831/10000000000 : ℝ)|=(5407242831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-934553103/5000000000 : ℝ)|^2209 ≤ (704302917461/6250000000000 : ℝ)^1697
        have hw : |(-934553103/5000000000 : ℝ)|=(934553103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s4_7 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (537140527/1250000000 : ℝ)*x 0 + (1118850857/2500000000 : ℝ)*x 1 + (257827021/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537140527/1250000000 : ℝ)^2209 ≤ (16652307543643/50000000000000 : ℝ)^1697 := by
    have hnat : (537140527 : ℕ)^2209*50000000000000^1697 ≤ 16652307543643^1697*1250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537140527 1250000000 16652307543643 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118850857/2500000000 : ℝ)^2209 ≤ (35114392159823/100000000000000 : ℝ)^1697 := by
    have hnat : (1118850857 : ℕ)^2209*100000000000000^1697 ≤ 35114392159823^1697*2500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118850857 2500000000 35114392159823 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257827021/625000000 : ℝ)^2209 ≤ (31580992745481/100000000000000 : ℝ)^1697 := by
    have hnat : (257827021 : ℕ)^2209*100000000000000^1697 ≤ 31580992745481^1697*625000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257827021 625000000 31580992745481 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537140527/1250000000 : ℝ), (1118850857/2500000000 : ℝ), (257827021/625000000 : ℝ)] ![(16652307543643/50000000000000 : ℝ), (35114392159823/100000000000000 : ℝ), (31580992745481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537140527/1250000000 : ℝ)|^2209 ≤ (16652307543643/50000000000000 : ℝ)^1697
        have hw : |(537140527/1250000000 : ℝ)|=(537140527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118850857/2500000000 : ℝ)|^2209 ≤ (35114392159823/100000000000000 : ℝ)^1697
        have hw : |(1118850857/2500000000 : ℝ)|=(1118850857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257827021/625000000 : ℝ)|^2209 ≤ (31580992745481/100000000000000 : ℝ)^1697
        have hw : |(257827021/625000000 : ℝ)|=(257827021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1458_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (711/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2959/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5623/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5623/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5623/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5623/50000 : ℝ) ^ (4417/1024 : ℝ) ≤ (251972113292511/3125000000000000000 : ℝ) := by
    have hpowers : (5623/50000 : ℝ)^4417 ≤ (251972113292511/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5623 : ℕ)^4417*3125000000000000000^1024 ≤ 251972113292511^1024*50000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5623 50000 251972113292511 3125000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5623/50000 : ℝ)) (X := (251972113292511/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14933/100000 : ℝ) ^ (4417/1024 : ℝ) ≤ (27396981800158583/100000000000000000000 : ℝ) := by
    have hpowers : (14933/100000 : ℝ)^4417 ≤ (27396981800158583/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14933 : ℕ)^4417*100000000000000000000^1024 ≤ 27396981800158583^1024*100000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14933 100000 27396981800158583 100000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14933/100000 : ℝ)) (X := (27396981800158583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562751972113292511/1562500000000000000 : ℝ) ≤ (5000186916704919/5000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (1562751972113292511/1562500000000000000 : ℝ)^1024 ≤ (5000186916704919/5000000000000000 : ℝ)^4417 := by
      have hnat : (1562751972113292511 : ℕ)^1024*5000000000000000^4417 ≤ 5000186916704919^4417*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562751972113292511 1562500000000000000 5000186916704919 5000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000186916704919/5000000000000000 : ℝ)) (X := (1562751972113292511/1562500000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007092017885103787/20000000000000000000 : ℝ) ≤ (5000410982421917/5000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (20007092017885103787/20000000000000000000 : ℝ)^1024 ≤ (5000410982421917/5000000000000000 : ℝ)^4417 := by
      have hnat : (20007092017885103787 : ℕ)^1024*5000000000000000^4417 ≤ 5000410982421917^4417*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007092017885103787 20000000000000000000 5000410982421917 5000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000410982421917/5000000000000000 : ℝ)) (X := (20007092017885103787/20000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027396981800158583/50000000000000000000 : ℝ) ≤ (1000127009627783/1000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50027396981800158583/50000000000000000000 : ℝ)^1024 ≤ (1000127009627783/1000000000000000 : ℝ)^4417 := by
      have hnat : (50027396981800158583 : ℕ)^1024*1000000000000000^4417 ≤ 1000127009627783^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027396981800158583 50000000000000000000 1000127009627783 1000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000127009627783/1000000000000000 : ℝ)) (X := (50027396981800158583/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(251972113292511/3125000000000000000 : ℝ) ≤ ((18430649475784317337/18435000000000000000 : ℝ)+2*(112032858499/92175000000000 : ℝ)*(5623/50000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (18430649475784317337/18435000000000000000 : ℝ)+2*(112032858499/92175000000000 : ℝ)*(5623/50000 : ℝ)=(5000186916704919/5000000000000000 : ℝ) by norm_num, show 1+2*(251972113292511/3125000000000000000 : ℝ)=(1562751972113292511/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27396981800158583/100000000000000000000 : ℝ)+(251972113292511/3125000000000000000 : ℝ) ≤ ((18430649475784317337/18435000000000000000 : ℝ)+(112032858499/92175000000000 : ℝ)*((14933/100000 : ℝ)+(5623/50000 : ℝ)))^(4417/1024 : ℝ) := by
    rw [show (18430649475784317337/18435000000000000000 : ℝ)+(112032858499/92175000000000 : ℝ)*((14933/100000 : ℝ)+(5623/50000 : ℝ))=(5000410982421917/5000000000000000 : ℝ) by norm_num, show 1+(27396981800158583/100000000000000000000 : ℝ)+(251972113292511/3125000000000000000 : ℝ)=(20007092017885103787/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27396981800158583/100000000000000000000 : ℝ) ≤ ((18430649475784317337/18435000000000000000 : ℝ)+2*(112032858499/92175000000000 : ℝ)*(14933/100000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (18430649475784317337/18435000000000000000 : ℝ)+2*(112032858499/92175000000000 : ℝ)*(14933/100000 : ℝ)=(1000127009627783/1000000000000000 : ℝ) by norm_num, show 1+2*(27396981800158583/100000000000000000000 : ℝ)=(50027396981800158583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18430649475784317337/18435000000000000000 : ℝ)*(X 1 0+X 2 0)+(112032858499/92175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (18430649475784317337/18435000000000000000 : ℝ)) (alpha := (112032858499/92175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18430649475784317337/18435000000000000000 : ℝ)*(X 0 1+X 2 1)+(112032858499/92175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (18430649475784317337/18435000000000000000 : ℝ)) (alpha := (112032858499/92175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18430649475784317337/18435000000000000000 : ℝ)*(X 0 2+X 1 2)+(112032858499/92175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (5623/50000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (18430649475784317337/18435000000000000000 : ℝ)) (alpha := (112032858499/92175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1947715269/10000000000 : ℝ)*X 0 0+(5407837443/10000000000 : ℝ)*X 0 1+(2623244217/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336747463/2500000000 : ℝ)*X 1 0+(-2029860453/10000000000 : ℝ)*X 1 1+(5246488577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267349483/500000000 : ℝ)*X 2 0+(5246488761/10000000000 : ℝ)*X 2 1+(-405972093/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148549411/5000000000 : ℝ)*X 0 0+(1030983211/2500000000 : ℝ)*X 0 1+(4476696333/10000000000 : ℝ)*X 0 2+(2148549411/5000000000 : ℝ)*X 1 0+(1030983211/2500000000 : ℝ)*X 1 1+(4476696333/10000000000 : ℝ)*X 1 2+(2148549411/5000000000 : ℝ)*X 2 0+(1030983211/2500000000 : ℝ)*X 2 1+(4476696333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-486931747/2500000000 : ℝ)*X 0 0+(209883191/400000000 : ℝ)*X 0 1+(5407242851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652463799/5000000000 : ℝ)*X 1 0+(-93455311/500000000 : ℝ)*X 1 1+(5407242847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663115953/1250000000 : ℝ)*X 2 0+(5407242831/10000000000 : ℝ)*X 2 1+(-934553103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537140527/1250000000 : ℝ)*X 0 0+(1118850857/2500000000 : ℝ)*X 0 1+(257827021/625000000 : ℝ)*X 0 2+(537140527/1250000000 : ℝ)*X 1 0+(1118850857/2500000000 : ℝ)*X 1 1+(257827021/625000000 : ℝ)*X 1 2+(537140527/1250000000 : ℝ)*X 2 0+(1118850857/2500000000 : ℝ)*X 2 1+(257827021/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1398875456608520656317450051/153625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1196314057/100000000000000 : ℝ)*(base19) + (790358943/100000000000000 : ℝ)*(base23) + (28843391/25000000000000 : ℝ)*(lower2) + (37086919/20000000000000 : ℝ)*(upper3) + (3461543/20000000000000 : ℝ)*(lower4) + (4516298201254923/100000000000000 : ℝ)*(major0) + (4516298201254923/100000000000000 : ℝ)*(major1) + (4516298201254923/100000000000000 : ℝ)*(major2) + (123955613053231/2000000000000 : ℝ)*(sp0) + (3098904404701783/50000000000000 : ℝ)*(sp1) + (154945230383967/2500000000000 : ℝ)*(sp2) + (708692970792057/25000000000000 : ℝ)*(sp3) + (29353056073/100000000000000 : ℝ)*(sp4) + (7105048993/50000000000000 : ℝ)*(sp7) + (566957218653243/20000000000000 : ℝ)*(f.failure) + (6197810005717623/100000000000000 : ℝ)*(f.sum) + (10725177419163/3072500000000000000000000000 : ℝ)*base65 + (984958489182199983/614500000000000000000000000000000 : ℝ)*base68 + (6253658984963199983/614500000000000000000000000000000 : ℝ)*base70 + (8852355732012300017/614500000000000000000000000000000 : ℝ)*base71 + (9527671392173/3072500000000000000000000000 : ℝ)*base73 + (6302308187368699983/614500000000000000000000000000000 : ℝ)*base76 + (719487439023699983/614500000000000000000000000000000 : ℝ)*base78 + (7393059893379699983/614500000000000000000000000000000 : ℝ)*base80 + (4472468779/384062500000000000000000000 : ℝ)*base82 + (120969/125000000000000000000 : ℝ)*base90 + (120969/125000000000000000000 : ℝ)*base92 + (120969/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (666013840841501632859743987/61450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352413823/20000000000000 : ℝ)*(base19) + (492019057/25000000000000 : ℝ)*(base23) + (6502427/3125000000000 : ℝ)*(upper3) + (19859177/25000000000000 : ℝ)*(lower4) + (230250431/100000000000000 : ℝ)*(upper5) + (909938214091817/20000000000000 : ℝ)*(major0) + (909938214091817/20000000000000 : ℝ)*(major1) + (909938214091817/20000000000000 : ℝ)*(major2) + (37243205699/100000000000000 : ℝ)*(sp1) + (20240157257/50000000000000 : ℝ)*(sp2) + (6243635679525273/100000000000000 : ℝ)*(sp4) + (6243596674250459/100000000000000 : ℝ)*(sp5) + (624359323113453/10000000000000 : ℝ)*(sp6) + (1427873050058027/50000000000000 : ℝ)*(sp7) + (1427873050058027/50000000000000 : ℝ)*(f.failure) + (6243635679525273/100000000000000 : ℝ)*(f.sum) + (869385061247/230437500000000000000000000 : ℝ)*base65 + (2443992918725789557/122900000000000000000000000000000 : ℝ)*base68 + (2056023277787789557/122900000000000000000000000000000 : ℝ)*base70 + (636221301486089557/122900000000000000000000000000000 : ℝ)*base72 + (16938085149463/3687000000000000000000000000 : ℝ)*base74 + (2630696767489489557/122900000000000000000000000000000 : ℝ)*base76 + (703613262083089557/122900000000000000000000000000000 : ℝ)*base78 + (136616456031889557/122900000000000000000000000000000 : ℝ)*base80 + (13934989599833/1843500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2608559/312500000000000000000 : ℝ)*base89 + (2608559/312500000000000000000 : ℝ)*base91 + (2608559/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1458_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1458_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1458_s5_0 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-243478097/1250000000 : ℝ)*x 0 + (5406865269/10000000000 : ℝ)*x 1 + (2623694137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243478097/1250000000 : ℝ)^2209 ≤ (5945258861489/50000000000000 : ℝ)^1697 := by
    have hnat : (243478097 : ℕ)^2209*50000000000000^1697 ≤ 5945258861489^1697*1250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243478097 1250000000 5945258861489 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406865269/10000000000 : ℝ)^2209 ≤ (22456540236523/50000000000000 : ℝ)^1697 := by
    have hnat : (5406865269 : ℕ)^2209*50000000000000^1697 ≤ 22456540236523^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406865269 10000000000 22456540236523 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623694137/5000000000 : ℝ)^2209 ≤ (43196401789419/100000000000000 : ℝ)^1697 := by
    have hnat : (2623694137 : ℕ)^2209*100000000000000^1697 ≤ 43196401789419^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623694137 5000000000 43196401789419 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243478097/1250000000 : ℝ), (5406865269/10000000000 : ℝ), (2623694137/5000000000 : ℝ)] ![(5945258861489/50000000000000 : ℝ), (22456540236523/50000000000000 : ℝ), (43196401789419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243478097/1250000000 : ℝ)|^2209 ≤ (5945258861489/50000000000000 : ℝ)^1697
        have hw : |(-243478097/1250000000 : ℝ)|=(243478097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406865269/10000000000 : ℝ)|^2209 ≤ (22456540236523/50000000000000 : ℝ)^1697
        have hw : |(5406865269/10000000000 : ℝ)|=(5406865269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623694137/5000000000 : ℝ)|^2209 ≤ (43196401789419/100000000000000 : ℝ)^1697
        have hw : |(2623694137/5000000000 : ℝ)|=(2623694137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s5_1 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534673757/1000000000 : ℝ)*x 0 + (-2029000093/10000000000 : ℝ)*x 1 + (2623694137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534673757/1000000000 : ℝ)^2209 ≤ (44264020730409/100000000000000 : ℝ)^1697 := by
    have hnat : (534673757 : ℕ)^2209*100000000000000^1697 ≤ 44264020730409^1697*1000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534673757 1000000000 44264020730409 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2029000093/10000000000 : ℝ)^2209 ≤ (12539577464611/100000000000000 : ℝ)^1697 := by
    have hnat : (2029000093 : ℕ)^2209*100000000000000^1697 ≤ 12539577464611^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029000093 10000000000 12539577464611 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623694137/5000000000 : ℝ)^2209 ≤ (43196401789419/100000000000000 : ℝ)^1697 := by
    have hnat : (2623694137 : ℕ)^2209*100000000000000^1697 ≤ 43196401789419^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623694137 5000000000 43196401789419 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534673757/1000000000 : ℝ), (-2029000093/10000000000 : ℝ), (2623694137/5000000000 : ℝ)] ![(44264020730409/100000000000000 : ℝ), (12539577464611/100000000000000 : ℝ), (43196401789419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534673757/1000000000 : ℝ)|^2209 ≤ (44264020730409/100000000000000 : ℝ)^1697
        have hw : |(534673757/1000000000 : ℝ)|=(534673757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2029000093/10000000000 : ℝ)|^2209 ≤ (12539577464611/100000000000000 : ℝ)^1697
        have hw : |(-2029000093/10000000000 : ℝ)|=(2029000093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623694137/5000000000 : ℝ)|^2209 ≤ (43196401789419/100000000000000 : ℝ)^1697
        have hw : |(2623694137/5000000000 : ℝ)|=(2623694137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s5_2 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673368783/5000000000 : ℝ)*x 0 + (131184707/250000000 : ℝ)*x 1 + (-202900009/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673368783/5000000000 : ℝ)^2209 ≤ (5533002585913/12500000000000 : ℝ)^1697 := by
    have hnat : (2673368783 : ℕ)^2209*12500000000000^1697 ≤ 5533002585913^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673368783 5000000000 5533002585913 12500000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131184707/250000000 : ℝ)^2209 ≤ (43196401853713/100000000000000 : ℝ)^1697 := by
    have hnat : (131184707 : ℕ)^2209*100000000000000^1697 ≤ 43196401853713^1697*250000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131184707 250000000 43196401853713 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202900009/1000000000 : ℝ)^2209 ≤ (3134894360119/25000000000000 : ℝ)^1697 := by
    have hnat : (202900009 : ℕ)^2209*25000000000000^1697 ≤ 3134894360119^1697*1000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202900009 1000000000 3134894360119 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673368783/5000000000 : ℝ), (131184707/250000000 : ℝ), (-202900009/1000000000 : ℝ)] ![(5533002585913/12500000000000 : ℝ), (43196401853713/100000000000000 : ℝ), (3134894360119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673368783/5000000000 : ℝ)|^2209 ≤ (5533002585913/12500000000000 : ℝ)^1697
        have hw : |(2673368783/5000000000 : ℝ)|=(2673368783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131184707/250000000 : ℝ)|^2209 ≤ (43196401853713/100000000000000 : ℝ)^1697
        have hw : |(131184707/250000000 : ℝ)|=(131184707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202900009/1000000000 : ℝ)|^2209 ≤ (3134894360119/25000000000000 : ℝ)^1697
        have hw : |(-202900009/1000000000 : ℝ)|=(202900009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s5_3 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297165201/10000000000 : ℝ)*x 0 + (2062985507/5000000000 : ℝ)*x 1 + (4474642161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297165201/10000000000 : ℝ)^2209 ≤ (33305028578179/100000000000000 : ℝ)^1697 := by
    have hnat : (4297165201 : ℕ)^2209*100000000000000^1697 ≤ 33305028578179^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297165201 10000000000 33305028578179 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062985507/5000000000 : ℝ)^2209 ≤ (15794177053389/50000000000000 : ℝ)^1697 := by
    have hnat : (2062985507 : ℕ)^2209*50000000000000^1697 ≤ 15794177053389^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062985507 5000000000 15794177053389 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474642161/10000000000 : ℝ)^2209 ≤ (35106617297671/100000000000000 : ℝ)^1697 := by
    have hnat : (4474642161 : ℕ)^2209*100000000000000^1697 ≤ 35106617297671^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474642161 10000000000 35106617297671 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297165201/10000000000 : ℝ), (2062985507/5000000000 : ℝ), (4474642161/10000000000 : ℝ)] ![(33305028578179/100000000000000 : ℝ), (15794177053389/50000000000000 : ℝ), (35106617297671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297165201/10000000000 : ℝ)|^2209 ≤ (33305028578179/100000000000000 : ℝ)^1697
        have hw : |(4297165201/10000000000 : ℝ)|=(4297165201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062985507/5000000000 : ℝ)|^2209 ≤ (15794177053389/50000000000000 : ℝ)^1697
        have hw : |(2062985507/5000000000 : ℝ)|=(2062985507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474642161/10000000000 : ℝ)|^2209 ≤ (35106617297671/100000000000000 : ℝ)^1697
        have hw : |(4474642161/10000000000 : ℝ)|=(4474642161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s5_4 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-389567183/2000000000 : ℝ)*x 0 + (2623982977/5000000000 : ℝ)*x 1 + (5406284579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389567183/2000000000 : ℝ)^2209 ≤ (11890606236849/100000000000000 : ℝ)^1697 := by
    have hnat : (389567183 : ℕ)^2209*100000000000000^1697 ≤ 11890606236849^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389567183 2000000000 11890606236849 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623982977/5000000000 : ℝ)^2209 ≤ (21601296052497/50000000000000 : ℝ)^1697 := by
    have hnat : (2623982977 : ℕ)^2209*50000000000000^1697 ≤ 21601296052497^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623982977 5000000000 21601296052497 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406284579/10000000000 : ℝ)^2209 ≤ (44906801646587/100000000000000 : ℝ)^1697 := by
    have hnat : (5406284579 : ℕ)^2209*100000000000000^1697 ≤ 44906801646587^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406284579 10000000000 44906801646587 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389567183/2000000000 : ℝ), (2623982977/5000000000 : ℝ), (5406284579/10000000000 : ℝ)] ![(11890606236849/100000000000000 : ℝ), (21601296052497/50000000000000 : ℝ), (44906801646587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389567183/2000000000 : ℝ)|^2209 ≤ (11890606236849/100000000000000 : ℝ)^1697
        have hw : |(-389567183/2000000000 : ℝ)|=(389567183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623982977/5000000000 : ℝ)|^2209 ≤ (21601296052497/50000000000000 : ℝ)^1697
        have hw : |(2623982977/5000000000 : ℝ)|=(2623982977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406284579/10000000000 : ℝ)|^2209 ≤ (44906801646587/100000000000000 : ℝ)^1697
        have hw : |(5406284579/10000000000 : ℝ)|=(5406284579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s5_5 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265258153/500000000 : ℝ)*x 0 + (-935051897/5000000000 : ℝ)*x 1 + (5406284627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265258153/500000000 : ℝ)^2209 ≤ (10954130359151/25000000000000 : ℝ)^1697 := by
    have hnat : (265258153 : ℕ)^2209*25000000000000^1697 ≤ 10954130359151^1697*500000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265258153 500000000 10954130359151 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935051897/5000000000 : ℝ)^2209 ≤ (11276676386943/100000000000000 : ℝ)^1697 := by
    have hnat : (935051897 : ℕ)^2209*100000000000000^1697 ≤ 11276676386943^1697*5000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935051897 5000000000 11276676386943 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406284627/10000000000 : ℝ)^2209 ≤ (11226700541397/25000000000000 : ℝ)^1697 := by
    have hnat : (5406284627 : ℕ)^2209*25000000000000^1697 ≤ 11226700541397^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406284627 10000000000 11226700541397 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265258153/500000000 : ℝ), (-935051897/5000000000 : ℝ), (5406284627/10000000000 : ℝ)] ![(10954130359151/25000000000000 : ℝ), (11276676386943/100000000000000 : ℝ), (11226700541397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265258153/500000000 : ℝ)|^2209 ≤ (10954130359151/25000000000000 : ℝ)^1697
        have hw : |(265258153/500000000 : ℝ)|=(265258153/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935051897/5000000000 : ℝ)|^2209 ≤ (11276676386943/100000000000000 : ℝ)^1697
        have hw : |(-935051897/5000000000 : ℝ)|=(935051897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406284627/10000000000 : ℝ)|^2209 ≤ (11226700541397/25000000000000 : ℝ)^1697
        have hw : |(5406284627/10000000000 : ℝ)|=(5406284627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s5_6 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305163059/10000000000 : ℝ)*x 0 + (5406284641/10000000000 : ℝ)*x 1 + (-74804151/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305163059/10000000000 : ℝ)^2209 ≤ (43816521425853/100000000000000 : ℝ)^1697 := by
    have hnat : (5305163059 : ℕ)^2209*100000000000000^1697 ≤ 43816521425853^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305163059 10000000000 43816521425853 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406284641/10000000000 : ℝ)^2209 ≤ (44906802316963/100000000000000 : ℝ)^1697 := by
    have hnat : (5406284641 : ℕ)^2209*100000000000000^1697 ≤ 44906802316963^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406284641 10000000000 44906802316963 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74804151/400000000 : ℝ)^2209 ≤ (11276676237807/100000000000000 : ℝ)^1697 := by
    have hnat : (74804151 : ℕ)^2209*100000000000000^1697 ≤ 11276676237807^1697*400000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74804151 400000000 11276676237807 100000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305163059/10000000000 : ℝ), (5406284641/10000000000 : ℝ), (-74804151/400000000 : ℝ)] ![(43816521425853/100000000000000 : ℝ), (44906802316963/100000000000000 : ℝ), (11276676237807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305163059/10000000000 : ℝ)|^2209 ≤ (43816521425853/100000000000000 : ℝ)^1697
        have hw : |(5305163059/10000000000 : ℝ)|=(5305163059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406284641/10000000000 : ℝ)|^2209 ≤ (44906802316963/100000000000000 : ℝ)^1697
        have hw : |(5406284641/10000000000 : ℝ)|=(5406284641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74804151/400000000 : ℝ)|^2209 ≤ (11276676237807/100000000000000 : ℝ)^1697
        have hw : |(-74804151/400000000 : ℝ)|=(74804151/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1458_s5_7 (p : ℝ) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4297189501/10000000000 : ℝ)*x 0 + (447337919/1000000000 : ℝ)*x 1 + (825448113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297189501/10000000000 : ℝ)^2209 ≤ (1332210949497/4000000000000 : ℝ)^1697 := by
    have hnat : (4297189501 : ℕ)^2209*4000000000000^1697 ≤ 1332210949497^1697*10000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297189501 10000000000 1332210949497 4000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447337919/1000000000 : ℝ)^2209 ≤ (17546859692481/50000000000000 : ℝ)^1697 := by
    have hnat : (447337919 : ℕ)^2209*50000000000000^1697 ≤ 17546859692481^1697*1000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447337919 1000000000 17546859692481 50000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825448113/2000000000 : ℝ)^2209 ≤ (7900251714781/25000000000000 : ℝ)^1697 := by
    have hnat : (825448113 : ℕ)^2209*25000000000000^1697 ≤ 7900251714781^1697*2000000000^2209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825448113 2000000000 7900251714781 25000000000000 2209 1697 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2209/512 : ℝ)) 2209 1697 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297189501/10000000000 : ℝ), (447337919/1000000000 : ℝ), (825448113/2000000000 : ℝ)] ![(1332210949497/4000000000000 : ℝ), (17546859692481/50000000000000 : ℝ), (7900251714781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297189501/10000000000 : ℝ)|^2209 ≤ (1332210949497/4000000000000 : ℝ)^1697
        have hw : |(4297189501/10000000000 : ℝ)|=(4297189501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447337919/1000000000 : ℝ)|^2209 ≤ (17546859692481/50000000000000 : ℝ)^1697
        have hw : |(447337919/1000000000 : ℝ)|=(447337919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825448113/2000000000 : ℝ)|^2209 ≤ (7900251714781/25000000000000 : ℝ)^1697
        have hw : |(825448113/2000000000 : ℝ)|=(825448113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1458_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2279/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (711/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (711/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (711/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (711/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (711/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (711/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (711/6250 : ℝ) ^ (4417/1024 : ℝ) ≤ (8472921703061087/100000000000000000000 : ℝ) := by
    have hpowers : (711/6250 : ℝ)^4417 ≤ (8472921703061087/100000000000000000000 : ℝ)^1024 := by
      have hnat : (711 : ℕ)^4417*100000000000000000000^1024 ≤ 8472921703061087^1024*6250^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        711 6250 8472921703061087 100000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (711/6250 : ℝ)) (X := (8472921703061087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2959/20000 : ℝ) ^ (4417/1024 : ℝ) ≤ (26321484017336959/100000000000000000000 : ℝ) := by
    have hpowers : (2959/20000 : ℝ)^4417 ≤ (26321484017336959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2959 : ℕ)^4417*100000000000000000000^1024 ≤ 26321484017336959^1024*20000^4417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2959 20000 26321484017336959 100000000000000000000 4417 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2959/20000 : ℝ)) (X := (26321484017336959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008472921703061087/50000000000000000000 : ℝ) ≤ (156256138008811/156250000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50008472921703061087/50000000000000000000 : ℝ)^1024 ≤ (156256138008811/156250000000000 : ℝ)^4417 := by
      have hnat : (50008472921703061087 : ℕ)^1024*156250000000000^4417 ≤ 156256138008811^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008472921703061087 50000000000000000000 156256138008811 156250000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156256138008811/156250000000000 : ℝ)) (X := (50008472921703061087/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017397202860199023/50000000000000000000 : ℝ) ≤ (10000806536357657/10000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50017397202860199023/50000000000000000000 : ℝ)^1024 ≤ (10000806536357657/10000000000000000 : ℝ)^4417 := by
      have hnat : (50017397202860199023 : ℕ)^1024*10000000000000000^4417 ≤ 10000806536357657^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017397202860199023 50000000000000000000 10000806536357657 10000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000806536357657/10000000000000000 : ℝ)) (X := (50017397202860199023/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026321484017336959/50000000000000000000 : ℝ) ≤ (1000122024015141/1000000000000000 : ℝ) ^ (4417/1024 : ℝ) := by
    have hpowers : (50026321484017336959/50000000000000000000 : ℝ)^1024 ≤ (1000122024015141/1000000000000000 : ℝ)^4417 := by
      have hnat : (50026321484017336959 : ℕ)^1024*1000000000000000^4417 ≤ 1000122024015141^4417*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026321484017336959 50000000000000000000 1000122024015141 1000000000000000 1024 4417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000122024015141/1000000000000000 : ℝ)) (X := (50026321484017336959/50000000000000000000 : ℝ)) (by norm_num) 4417 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8472921703061087/100000000000000000000 : ℝ) ≤ ((213637065661378247/213687500000000000 : ℝ)+2*(413703793753/341900000000000 : ℝ)*(711/6250 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (213637065661378247/213687500000000000 : ℝ)+2*(413703793753/341900000000000 : ℝ)*(711/6250 : ℝ)=(156256138008811/156250000000000 : ℝ) by norm_num, show 1+2*(8472921703061087/100000000000000000000 : ℝ)=(50008472921703061087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26321484017336959/100000000000000000000 : ℝ)+(8472921703061087/100000000000000000000 : ℝ) ≤ ((213637065661378247/213687500000000000 : ℝ)+(413703793753/341900000000000 : ℝ)*((2959/20000 : ℝ)+(711/6250 : ℝ)))^(4417/1024 : ℝ) := by
    rw [show (213637065661378247/213687500000000000 : ℝ)+(413703793753/341900000000000 : ℝ)*((2959/20000 : ℝ)+(711/6250 : ℝ))=(10000806536357657/10000000000000000 : ℝ) by norm_num, show 1+(26321484017336959/100000000000000000000 : ℝ)+(8472921703061087/100000000000000000000 : ℝ)=(50017397202860199023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26321484017336959/100000000000000000000 : ℝ) ≤ ((213637065661378247/213687500000000000 : ℝ)+2*(413703793753/341900000000000 : ℝ)*(2959/20000 : ℝ))^(4417/1024 : ℝ) := by
    rw [show (213637065661378247/213687500000000000 : ℝ)+2*(413703793753/341900000000000 : ℝ)*(2959/20000 : ℝ)=(1000122024015141/1000000000000000 : ℝ) by norm_num, show 1+2*(26321484017336959/100000000000000000000 : ℝ)=(50026321484017336959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (213637065661378247/213687500000000000 : ℝ)*(X 1 0+X 2 0)+(413703793753/341900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (213637065661378247/213687500000000000 : ℝ)) (alpha := (413703793753/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (213637065661378247/213687500000000000 : ℝ)*(X 0 1+X 2 1)+(413703793753/341900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (213637065661378247/213687500000000000 : ℝ)) (alpha := (413703793753/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (213637065661378247/213687500000000000 : ℝ)*(X 0 2+X 1 2)+(413703793753/341900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4417/1024 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (213637065661378247/213687500000000000 : ℝ)) (alpha := (413703793753/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-243478097/1250000000 : ℝ)*X 0 0+(5406865269/10000000000 : ℝ)*X 0 1+(2623694137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534673757/1000000000 : ℝ)*X 1 0+(-2029000093/10000000000 : ℝ)*X 1 1+(2623694137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673368783/5000000000 : ℝ)*X 2 0+(131184707/250000000 : ℝ)*X 2 1+(-202900009/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297165201/10000000000 : ℝ)*X 0 0+(2062985507/5000000000 : ℝ)*X 0 1+(4474642161/10000000000 : ℝ)*X 0 2+(4297165201/10000000000 : ℝ)*X 1 0+(2062985507/5000000000 : ℝ)*X 1 1+(4474642161/10000000000 : ℝ)*X 1 2+(4297165201/10000000000 : ℝ)*X 2 0+(2062985507/5000000000 : ℝ)*X 2 1+(4474642161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-389567183/2000000000 : ℝ)*X 0 0+(2623982977/5000000000 : ℝ)*X 0 1+(5406284579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265258153/500000000 : ℝ)*X 1 0+(-935051897/5000000000 : ℝ)*X 1 1+(5406284627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305163059/10000000000 : ℝ)*X 2 0+(5406284641/10000000000 : ℝ)*X 2 1+(-74804151/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4297189501/10000000000 : ℝ)*X 0 0+(447337919/1000000000 : ℝ)*X 0 1+(825448113/2000000000 : ℝ)*X 0 2+(4297189501/10000000000 : ℝ)*X 1 0+(447337919/1000000000 : ℝ)*X 1 1+(825448113/2000000000 : ℝ)*X 1 2+(4297189501/10000000000 : ℝ)*X 2 0+(447337919/1000000000 : ℝ)*X 2 1+(825448113/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1458_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105833331078714539989799493/10684375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1778382463/100000000000000 : ℝ)*(base19) + (13239243/800000000000 : ℝ)*(base23) + (6351173/10000000000000 : ℝ)*(lower2) + (15177247/6250000000000 : ℝ)*(upper3) + (159661541/100000000000000 : ℝ)*(upper5) + (4569320944732473/100000000000000 : ℝ)*(major0) + (4569320944732473/100000000000000 : ℝ)*(major1) + (4569320944732473/100000000000000 : ℝ)*(major2) + (1254107257578387/20000000000000 : ℝ)*(sp0) + (6270572418520823/100000000000000 : ℝ)*(sp1) + (6270572541997911/100000000000000 : ℝ)*(sp2) + (573609748597781/20000000000000 : ℝ)*(sp3) + (4738626419/12500000000000 : ℝ)*(sp4) + (930969587/5000000000000 : ℝ)*(sp7) + (573613472476129/20000000000000 : ℝ)*(f.failure) + (3135287098451643/50000000000000 : ℝ)*(f.sum) + (59724134302153/8547500000000000000000000000 : ℝ)*base66 + (163537335493986647/10684375000000000000000000000000 : ℝ)*base68 + (90890660793955397/10684375000000000000000000000000 : ℝ)*base70 + (45228515627980397/10684375000000000000000000000000 : ℝ)*base72 + (34480818722569/4273750000000000000000000000 : ℝ)*base74 + (2032116935130397/10684375000000000000000000000000 : ℝ)*base76 + (5246560496382103/10684375000000000000000000000000 : ℝ)*base77 + (66243754032408239/5342187500000000000000000000000 : ℝ)*base79 + (15285790746407/2136875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (135893/125000000000000000000 : ℝ)*base89 + (135893/125000000000000000000 : ℝ)*base91 + (135893/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9320373547206601358161743/2136875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (314236501/50000000000000 : ℝ)*(base19) + (331661719/50000000000000 : ℝ)*(base23) + (24138717/25000000000000 : ℝ)*(upper3) + (6003581/50000000000000 : ℝ)*(lower4) + (82039189/100000000000000 : ℝ)*(upper5) + (115067396275447/2500000000000 : ℝ)*(major0) + (115067396275447/2500000000000 : ℝ)*(major1) + (115067396275447/2500000000000 : ℝ)*(major2) + (14000720521/100000000000000 : ℝ)*(sp1) + (7855836961/50000000000000 : ℝ)*(sp2) + (6316375462364887/100000000000000 : ℝ)*(sp4) + (6316360833171363/100000000000000 : ℝ)*(sp5) + (6316359087367527/100000000000000 : ℝ)*(sp6) + (722254023570349/25000000000000 : ℝ)*(sp7) + (722254023570349/25000000000000 : ℝ)*(f.failure) + (6316375462364887/100000000000000 : ℝ)*(f.sum) + (9144964857701/3419000000000000000000000000 : ℝ)*base66 + (8524271156640943/1068437500000000000000000000000 : ℝ)*base67 + (17144060892891261/2136875000000000000000000000000 : ℝ)*base69 + (5956450750499693/1068437500000000000000000000000 : ℝ)*base71 + (6586596837993/3419000000000000000000000000 : ℝ)*base73 + (22633842814980011/2136875000000000000000000000000 : ℝ)*base75 + (2956359831941239/2136875000000000000000000000000 : ℝ)*base78 + (37294087200650011/2136875000000000000000000000000 : ℝ)*base79 + (25199045556363/3419000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (706367/156250000000000000000 : ℝ)*base90 + (706367/156250000000000000000 : ℝ)*base92 + (706367/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1458_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1458_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1458_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7857/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1458_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1458_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1458_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4417/1024 : ℝ) ≤ p) (hpb : p ≤ (2209/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9957317/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7857/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1458_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
