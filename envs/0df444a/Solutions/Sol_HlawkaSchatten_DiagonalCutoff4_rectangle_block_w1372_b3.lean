-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:45.521965+00:00
-- url     : https://prove2.me/submissions/ad7a20cd-e27d-49af-8c2d-86175be199f7

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
theorem support_rectangle_w1372_box_0 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853427603/10000000000 : ℝ)*x 0 + (5388680581/10000000000 : ℝ)*x 1 + (5388680437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853427603/10000000000 : ℝ)^1083 ≤ (2749891682833/25000000000000 : ℝ)^827 := by
    have hnat : (1853427603 : ℕ)^1083*25000000000000^827 ≤ 2749891682833^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853427603 10000000000 2749891682833 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388680581/10000000000 : ℝ)^1083 ≤ (356001739247/800000000000 : ℝ)^827 := by
    have hnat : (5388680581 : ℕ)^1083*800000000000^827 ≤ 356001739247^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388680581 10000000000 356001739247 800000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388680437/10000000000 : ℝ)^1083 ≤ (222501079243/500000000000 : ℝ)^827 := by
    have hnat : (5388680437 : ℕ)^1083*500000000000^827 ≤ 222501079243^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388680437 10000000000 222501079243 500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853427603/10000000000 : ℝ), (5388680581/10000000000 : ℝ), (5388680437/10000000000 : ℝ)] ![(2749891682833/25000000000000 : ℝ), (356001739247/800000000000 : ℝ), (222501079243/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853427603/10000000000 : ℝ)|^1083 ≤ (2749891682833/25000000000000 : ℝ)^827
        have hw : |(-1853427603/10000000000 : ℝ)|=(1853427603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388680581/10000000000 : ℝ)|^1083 ≤ (356001739247/800000000000 : ℝ)^827
        have hw : |(5388680581/10000000000 : ℝ)|=(5388680581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388680437/10000000000 : ℝ)|^1083 ≤ (222501079243/500000000000 : ℝ)^827
        have hw : |(5388680437/10000000000 : ℝ)|=(5388680437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_1 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1057108359/2000000000 : ℝ)*x 0 + (-997437441/5000000000 : ℝ)*x 1 + (5388680303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057108359/2000000000 : ℝ)^1083 ≤ (10847037918119/25000000000000 : ℝ)^827 := by
    have hnat : (1057108359 : ℕ)^1083*25000000000000^827 ≤ 10847037918119^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057108359 2000000000 10847037918119 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997437441/5000000000 : ℝ)^1083 ≤ (12111633908587/100000000000000 : ℝ)^827 := by
    have hnat : (997437441 : ℕ)^1083*100000000000000^827 ≤ 12111633908587^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997437441 5000000000 12111633908587 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388680303/10000000000 : ℝ)^1083 ≤ (4450021439947/10000000000000 : ℝ)^827 := by
    have hnat : (5388680303 : ℕ)^1083*10000000000000^827 ≤ 4450021439947^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388680303 10000000000 4450021439947 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057108359/2000000000 : ℝ), (-997437441/5000000000 : ℝ), (5388680303/10000000000 : ℝ)] ![(10847037918119/25000000000000 : ℝ), (12111633908587/100000000000000 : ℝ), (4450021439947/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057108359/2000000000 : ℝ)|^1083 ≤ (10847037918119/25000000000000 : ℝ)^827
        have hw : |(1057108359/2000000000 : ℝ)|=(1057108359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-997437441/5000000000 : ℝ)|^1083 ≤ (12111633908587/100000000000000 : ℝ)^827
        have hw : |(-997437441/5000000000 : ℝ)|=(997437441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388680303/10000000000 : ℝ)|^1083 ≤ (4450021439947/10000000000000 : ℝ)^827
        have hw : |(5388680303/10000000000 : ℝ)|=(5388680303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_2 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (264277061/500000000 : ℝ)*x 0 + (5388680961/10000000000 : ℝ)*x 1 + (-398974953/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264277061/500000000 : ℝ)^1083 ≤ (21694072745641/50000000000000 : ℝ)^827 := by
    have hnat : (264277061 : ℕ)^1083*50000000000000^827 ≤ 21694072745641^827*500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264277061 500000000 21694072745641 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388680961/10000000000 : ℝ)^1083 ≤ (44500221515349/100000000000000 : ℝ)^827 := by
    have hnat : (5388680961 : ℕ)^1083*100000000000000^827 ≤ 44500221515349^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388680961 10000000000 44500221515349 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398974953/2000000000 : ℝ)^1083 ≤ (6055816489173/50000000000000 : ℝ)^827 := by
    have hnat : (398974953 : ℕ)^1083*50000000000000^827 ≤ 6055816489173^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398974953 2000000000 6055816489173 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264277061/500000000 : ℝ), (5388680961/10000000000 : ℝ), (-398974953/2000000000 : ℝ)] ![(21694072745641/50000000000000 : ℝ), (44500221515349/100000000000000 : ℝ), (6055816489173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264277061/500000000 : ℝ)|^1083 ≤ (21694072745641/50000000000000 : ℝ)^827
        have hw : |(264277061/500000000 : ℝ)|=(264277061/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388680961/10000000000 : ℝ)|^1083 ≤ (44500221515349/100000000000000 : ℝ)^827
        have hw : |(5388680961/10000000000 : ℝ)|=(5388680961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398974953/2000000000 : ℝ)|^1083 ≤ (6055816489173/50000000000000 : ℝ)^827
        have hw : |(-398974953/2000000000 : ℝ)|=(398974953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_3 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (893267739/2000000000 : ℝ)*x 0 + (2124455793/5000000000 : ℝ)*x 1 + (4248911903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893267739/2000000000 : ℝ)^1083 ≤ (1392044983077/4000000000000 : ℝ)^827 := by
    have hnat : (893267739 : ℕ)^1083*4000000000000^827 ≤ 1392044983077^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893267739 2000000000 1392044983077 4000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124455793/5000000000 : ℝ)^1083 ≤ (16299718056149/50000000000000 : ℝ)^827 := by
    have hnat : (2124455793 : ℕ)^1083*50000000000000^827 ≤ 16299718056149^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124455793 5000000000 16299718056149 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248911903/10000000000 : ℝ)^1083 ≤ (4074929912167/12500000000000 : ℝ)^827 := by
    have hnat : (4248911903 : ℕ)^1083*12500000000000^827 ≤ 4074929912167^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248911903 10000000000 4074929912167 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(893267739/2000000000 : ℝ), (2124455793/5000000000 : ℝ), (4248911903/10000000000 : ℝ)] ![(1392044983077/4000000000000 : ℝ), (16299718056149/50000000000000 : ℝ), (4074929912167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(893267739/2000000000 : ℝ)|^1083 ≤ (1392044983077/4000000000000 : ℝ)^827
        have hw : |(893267739/2000000000 : ℝ)|=(893267739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124455793/5000000000 : ℝ)|^1083 ≤ (16299718056149/50000000000000 : ℝ)^827
        have hw : |(2124455793/5000000000 : ℝ)|=(2124455793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248911903/10000000000 : ℝ)|^1083 ≤ (4074929912167/12500000000000 : ℝ)^827
        have hw : |(4248911903/10000000000 : ℝ)|=(4248911903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_4 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-218598933/1000000000 : ℝ)*x 0 + (1053110647/2000000000 : ℝ)*x 1 + (2632776507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218598933/1000000000 : ℝ)^1083 ≤ (6826598727763/50000000000000 : ℝ)^827 := by
    have hnat : (218598933 : ℕ)^1083*50000000000000^827 ≤ 6826598727763^827*1000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218598933 1000000000 6826598727763 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053110647/2000000000 : ℝ)^1083 ≤ (2698337653303/6250000000000 : ℝ)^827 := by
    have hnat : (1053110647 : ℕ)^1083*6250000000000^827 ≤ 2698337653303^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053110647 2000000000 2698337653303 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632776507/5000000000 : ℝ)^1083 ≤ (1349168752497/3125000000000 : ℝ)^827 := by
    have hnat : (2632776507 : ℕ)^1083*3125000000000^827 ≤ 1349168752497^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632776507 5000000000 1349168752497 3125000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218598933/1000000000 : ℝ), (1053110647/2000000000 : ℝ), (2632776507/5000000000 : ℝ)] ![(6826598727763/50000000000000 : ℝ), (2698337653303/6250000000000 : ℝ), (1349168752497/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218598933/1000000000 : ℝ)|^1083 ≤ (6826598727763/50000000000000 : ℝ)^827
        have hw : |(-218598933/1000000000 : ℝ)|=(218598933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053110647/2000000000 : ℝ)|^1083 ≤ (2698337653303/6250000000000 : ℝ)^827
        have hw : |(1053110647/2000000000 : ℝ)|=(1053110647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632776507/5000000000 : ℝ)|^1083 ≤ (1349168752497/3125000000000 : ℝ)^827
        have hw : |(2632776507/5000000000 : ℝ)|=(2632776507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_5 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1342978621/2500000000 : ℝ)*x 0 + (-1022243939/5000000000 : ℝ)*x 1 + (658194179/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342978621/2500000000 : ℝ)^1083 ≤ (44318989416547/100000000000000 : ℝ)^827 := by
    have hnat : (1342978621 : ℕ)^1083*100000000000000^827 ≤ 44318989416547^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342978621 2500000000 44318989416547 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022243939/5000000000 : ℝ)^1083 ≤ (3126901498459/25000000000000 : ℝ)^827 := by
    have hnat : (1022243939 : ℕ)^1083*25000000000000^827 ≤ 3126901498459^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022243939 5000000000 3126901498459 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658194179/1250000000 : ℝ)^1083 ≤ (43173404568097/100000000000000 : ℝ)^827 := by
    have hnat : (658194179 : ℕ)^1083*100000000000000^827 ≤ 43173404568097^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658194179 1250000000 43173404568097 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342978621/2500000000 : ℝ), (-1022243939/5000000000 : ℝ), (658194179/1250000000 : ℝ)] ![(44318989416547/100000000000000 : ℝ), (3126901498459/25000000000000 : ℝ), (43173404568097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342978621/2500000000 : ℝ)|^1083 ≤ (44318989416547/100000000000000 : ℝ)^827
        have hw : |(1342978621/2500000000 : ℝ)|=(1342978621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022243939/5000000000 : ℝ)|^1083 ≤ (3126901498459/25000000000000 : ℝ)^827
        have hw : |(-1022243939/5000000000 : ℝ)|=(1022243939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658194179/1250000000 : ℝ)|^1083 ≤ (43173404568097/100000000000000 : ℝ)^827
        have hw : |(658194179/1250000000 : ℝ)|=(658194179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_6 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074383009/2000000000 : ℝ)*x 0 + (1053110599/2000000000 : ℝ)*x 1 + (-511121927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074383009/2000000000 : ℝ)^1083 ≤ (44318995477579/100000000000000 : ℝ)^827 := by
    have hnat : (1074383009 : ℕ)^1083*100000000000000^827 ≤ 44318995477579^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074383009 2000000000 44318995477579 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053110599/2000000000 : ℝ)^1083 ≤ (8634679975179/20000000000000 : ℝ)^827 := by
    have hnat : (1053110599 : ℕ)^1083*20000000000000^827 ≤ 8634679975179^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053110599 2000000000 8634679975179 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511121927/2500000000 : ℝ)^1083 ≤ (2501520926377/20000000000000 : ℝ)^827 := by
    have hnat : (511121927 : ℕ)^1083*20000000000000^827 ≤ 2501520926377^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511121927 2500000000 2501520926377 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074383009/2000000000 : ℝ), (1053110599/2000000000 : ℝ), (-511121927/2500000000 : ℝ)] ![(44318995477579/100000000000000 : ℝ), (8634679975179/20000000000000 : ℝ), (2501520926377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074383009/2000000000 : ℝ)|^1083 ≤ (44318995477579/100000000000000 : ℝ)^827
        have hw : |(1074383009/2000000000 : ℝ)|=(1074383009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053110599/2000000000 : ℝ)|^1083 ≤ (8634679975179/20000000000000 : ℝ)^827
        have hw : |(1053110599/2000000000 : ℝ)|=(1053110599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511121927/2500000000 : ℝ)|^1083 ≤ (2501520926377/20000000000000 : ℝ)^827
        have hw : |(-511121927/2500000000 : ℝ)|=(511121927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_7 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (834073549/2000000000 : ℝ)*x 0 + (879368909/2000000000 : ℝ)*x 1 + (4396844663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834073549/2000000000 : ℝ)^1083 ≤ (31812539319453/100000000000000 : ℝ)^827 := by
    have hnat : (834073549 : ℕ)^1083*100000000000000^827 ≤ 31812539319453^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834073549 2000000000 31812539319453 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879368909/2000000000 : ℝ)^1083 ≤ (6818745946717/20000000000000 : ℝ)^827 := by
    have hnat : (879368909 : ℕ)^1083*20000000000000^827 ≤ 6818745946717^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879368909 2000000000 6818745946717 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4396844663/10000000000 : ℝ)^1083 ≤ (3409373093181/10000000000000 : ℝ)^827 := by
    have hnat : (4396844663 : ℕ)^1083*10000000000000^827 ≤ 3409373093181^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396844663 10000000000 3409373093181 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834073549/2000000000 : ℝ), (879368909/2000000000 : ℝ), (4396844663/10000000000 : ℝ)] ![(31812539319453/100000000000000 : ℝ), (6818745946717/20000000000000 : ℝ), (3409373093181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834073549/2000000000 : ℝ)|^1083 ≤ (31812539319453/100000000000000 : ℝ)^827
        have hw : |(834073549/2000000000 : ℝ)|=(834073549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(879368909/2000000000 : ℝ)|^1083 ≤ (6818745946717/20000000000000 : ℝ)^827
        have hw : |(879368909/2000000000 : ℝ)|=(879368909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4396844663/10000000000 : ℝ)|^1083 ≤ (3409373093181/10000000000000 : ℝ)^827
        have hw : |(4396844663/10000000000 : ℝ)|=(4396844663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_8 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058037957/5000000000 : ℝ)*x 0 + (5180648967/10000000000 : ℝ)*x 1 + (675335781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058037957/5000000000 : ℝ)^1083 ≤ (13084215456853/100000000000000 : ℝ)^827 := by
    have hnat : (1058037957 : ℕ)^1083*100000000000000^827 ≤ 13084215456853^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058037957 5000000000 13084215456853 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180648967/10000000000 : ℝ)^1083 ≤ (42264043263009/100000000000000 : ℝ)^827 := by
    have hnat : (5180648967 : ℕ)^1083*100000000000000^827 ≤ 42264043263009^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180648967 10000000000 42264043263009 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675335781/1250000000 : ℝ)^1083 ≤ (8930348251581/20000000000000 : ℝ)^827 := by
    have hnat : (675335781 : ℕ)^1083*20000000000000^827 ≤ 8930348251581^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675335781 1250000000 8930348251581 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058037957/5000000000 : ℝ), (5180648967/10000000000 : ℝ), (675335781/1250000000 : ℝ)] ![(13084215456853/100000000000000 : ℝ), (42264043263009/100000000000000 : ℝ), (8930348251581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058037957/5000000000 : ℝ)|^1083 ≤ (13084215456853/100000000000000 : ℝ)^827
        have hw : |(-1058037957/5000000000 : ℝ)|=(1058037957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180648967/10000000000 : ℝ)|^1083 ≤ (42264043263009/100000000000000 : ℝ)^827
        have hw : |(5180648967/10000000000 : ℝ)|=(5180648967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675335781/1250000000 : ℝ)|^1083 ≤ (8930348251581/20000000000000 : ℝ)^827
        have hw : |(675335781/1250000000 : ℝ)|=(675335781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_9 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5275712123/10000000000 : ℝ)*x 0 + (-1989100661/10000000000 : ℝ)*x 1 + (216107449/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275712123/10000000000 : ℝ)^1083 ≤ (21641257035477/50000000000000 : ℝ)^827 := by
    have hnat : (5275712123 : ℕ)^1083*50000000000000^827 ≤ 21641257035477^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275712123 10000000000 21641257035477 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989100661/10000000000 : ℝ)^1083 ≤ (12065744899177/100000000000000 : ℝ)^827 := by
    have hnat : (1989100661 : ℕ)^1083*100000000000000^827 ≤ 12065744899177^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989100661 10000000000 12065744899177 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216107449/400000000 : ℝ)^1083 ≤ (22325870504487/50000000000000 : ℝ)^827 := by
    have hnat : (216107449 : ℕ)^1083*50000000000000^827 ≤ 22325870504487^827*400000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216107449 400000000 22325870504487 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275712123/10000000000 : ℝ), (-1989100661/10000000000 : ℝ), (216107449/400000000 : ℝ)] ![(21641257035477/50000000000000 : ℝ), (12065744899177/100000000000000 : ℝ), (22325870504487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275712123/10000000000 : ℝ)|^1083 ≤ (21641257035477/50000000000000 : ℝ)^827
        have hw : |(5275712123/10000000000 : ℝ)|=(5275712123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989100661/10000000000 : ℝ)|^1083 ≤ (12065744899177/100000000000000 : ℝ)^827
        have hw : |(-1989100661/10000000000 : ℝ)|=(1989100661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216107449/400000000 : ℝ)|^1083 ≤ (22325870504487/50000000000000 : ℝ)^827
        have hw : |(216107449/400000000 : ℝ)|=(216107449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_10 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (659463993/1250000000 : ℝ)*x 0 + (337667861/625000000 : ℝ)*x 1 + (-397820303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659463993/1250000000 : ℝ)^1083 ≤ (4328251214783/10000000000000 : ℝ)^827 := by
    have hnat : (659463993 : ℕ)^1083*10000000000000^827 ≤ 4328251214783^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659463993 1250000000 4328251214783 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337667861/625000000 : ℝ)^1083 ≤ (44651736149403/100000000000000 : ℝ)^827 := by
    have hnat : (337667861 : ℕ)^1083*100000000000000^827 ≤ 44651736149403^827*625000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337667861 625000000 44651736149403 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397820303/2000000000 : ℝ)^1083 ≤ (6032875841529/50000000000000 : ℝ)^827 := by
    have hnat : (397820303 : ℕ)^1083*50000000000000^827 ≤ 6032875841529^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397820303 2000000000 6032875841529 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659463993/1250000000 : ℝ), (337667861/625000000 : ℝ), (-397820303/2000000000 : ℝ)] ![(4328251214783/10000000000000 : ℝ), (44651736149403/100000000000000 : ℝ), (6032875841529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659463993/1250000000 : ℝ)|^1083 ≤ (4328251214783/10000000000000 : ℝ)^827
        have hw : |(659463993/1250000000 : ℝ)|=(659463993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337667861/625000000 : ℝ)|^1083 ≤ (44651736149403/100000000000000 : ℝ)^827
        have hw : |(337667861/625000000 : ℝ)|=(337667861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397820303/2000000000 : ℝ)|^1083 ≤ (6032875841529/50000000000000 : ℝ)^827
        have hw : |(-397820303/2000000000 : ℝ)|=(397820303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_11 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2249723641/5000000000 : ℝ)*x 0 + (4232069663/10000000000 : ℝ)*x 1 + (66126103/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2249723641/5000000000 : ℝ)^1083 ≤ (4392418372483/12500000000000 : ℝ)^827 := by
    have hnat : (2249723641 : ℕ)^1083*12500000000000^827 ≤ 4392418372483^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249723641 5000000000 4392418372483 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232069663/10000000000 : ℝ)^1083 ≤ (8107580460997/25000000000000 : ℝ)^827 := by
    have hnat : (4232069663 : ℕ)^1083*25000000000000^827 ≤ 8107580460997^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232069663 10000000000 8107580460997 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66126103/156250000 : ℝ)^1083 ≤ (3243033116659/10000000000000 : ℝ)^827 := by
    have hnat : (66126103 : ℕ)^1083*10000000000000^827 ≤ 3243033116659^827*156250000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66126103 156250000 3243033116659 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2249723641/5000000000 : ℝ), (4232069663/10000000000 : ℝ), (66126103/156250000 : ℝ)] ![(4392418372483/12500000000000 : ℝ), (8107580460997/25000000000000 : ℝ), (3243033116659/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2249723641/5000000000 : ℝ)|^1083 ≤ (4392418372483/12500000000000 : ℝ)^827
        have hw : |(2249723641/5000000000 : ℝ)|=(2249723641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232069663/10000000000 : ℝ)|^1083 ≤ (8107580460997/25000000000000 : ℝ)^827
        have hw : |(4232069663/10000000000 : ℝ)|=(4232069663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66126103/156250000 : ℝ)|^1083 ≤ (3243033116659/10000000000000 : ℝ)^827
        have hw : |(66126103/156250000 : ℝ)|=(66126103/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_12 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-615559/3200000 : ℝ)*x 0 + (170982673/312500000 : ℝ)*x 1 + (2627230191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (615559/3200000 : ℝ)^1083 ≤ (5774137289073/50000000000000 : ℝ)^827 := by
    have hnat : (615559 : ℕ)^1083*50000000000000^827 ≤ 5774137289073^827*3200000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615559 3200000 5774137289073 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170982673/312500000 : ℝ)^1083 ≤ (45397391429677/100000000000000 : ℝ)^827 := by
    have hnat : (170982673 : ℕ)^1083*100000000000000^827 ≤ 45397391429677^827*312500000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170982673 312500000 45397391429677 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627230191/5000000000 : ℝ)^1083 ≤ (21527166991371/50000000000000 : ℝ)^827 := by
    have hnat : (2627230191 : ℕ)^1083*50000000000000^827 ≤ 21527166991371^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627230191 5000000000 21527166991371 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-615559/3200000 : ℝ), (170982673/312500000 : ℝ), (2627230191/5000000000 : ℝ)] ![(5774137289073/50000000000000 : ℝ), (45397391429677/100000000000000 : ℝ), (21527166991371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-615559/3200000 : ℝ)|^1083 ≤ (5774137289073/50000000000000 : ℝ)^827
        have hw : |(-615559/3200000 : ℝ)|=(615559/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170982673/312500000 : ℝ)|^1083 ≤ (45397391429677/100000000000000 : ℝ)^827
        have hw : |(170982673/312500000 : ℝ)|=(170982673/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627230191/5000000000 : ℝ)|^1083 ≤ (21527166991371/50000000000000 : ℝ)^827
        have hw : |(2627230191/5000000000 : ℝ)|=(2627230191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_13 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5379694133/10000000000 : ℝ)*x 0 + (-2048854327/10000000000 : ℝ)*x 1 + (1050892213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379694133/10000000000 : ℝ)^1083 ≤ (44403059409597/100000000000000 : ℝ)^827 := by
    have hnat : (5379694133 : ℕ)^1083*100000000000000^827 ≤ 44403059409597^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379694133 10000000000 44403059409597 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2048854327/10000000000 : ℝ)^1083 ≤ (12542599258107/100000000000000 : ℝ)^827 := by
    have hnat : (2048854327 : ℕ)^1083*100000000000000^827 ≤ 12542599258107^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048854327 10000000000 12542599258107 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050892213/2000000000 : ℝ)^1083 ≤ (21527170655767/50000000000000 : ℝ)^827 := by
    have hnat : (1050892213 : ℕ)^1083*50000000000000^827 ≤ 21527170655767^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050892213 2000000000 21527170655767 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379694133/10000000000 : ℝ), (-2048854327/10000000000 : ℝ), (1050892213/2000000000 : ℝ)] ![(44403059409597/100000000000000 : ℝ), (12542599258107/100000000000000 : ℝ), (21527170655767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379694133/10000000000 : ℝ)|^1083 ≤ (44403059409597/100000000000000 : ℝ)^827
        have hw : |(5379694133/10000000000 : ℝ)|=(5379694133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2048854327/10000000000 : ℝ)|^1083 ≤ (12542599258107/100000000000000 : ℝ)^827
        have hw : |(-2048854327/10000000000 : ℝ)|=(2048854327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050892213/2000000000 : ℝ)|^1083 ≤ (21527170655767/50000000000000 : ℝ)^827
        have hw : |(1050892213/2000000000 : ℝ)|=(1050892213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_14 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (215187779/400000000 : ℝ)*x 0 + (262723027/500000000 : ℝ)*x 1 + (-2048854569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215187779/400000000 : ℝ)^1083 ≤ (44403063106213/100000000000000 : ℝ)^827 := by
    have hnat : (215187779 : ℕ)^1083*100000000000000^827 ≤ 44403063106213^827*400000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215187779 400000000 44403063106213 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262723027/500000000 : ℝ)^1083 ≤ (43054335678129/100000000000000 : ℝ)^827 := by
    have hnat : (262723027 : ℕ)^1083*100000000000000^827 ≤ 43054335678129^827*500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262723027 500000000 43054335678129 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048854569/10000000000 : ℝ)^1083 ≤ (6271300599083/50000000000000 : ℝ)^827 := by
    have hnat : (2048854569 : ℕ)^1083*50000000000000^827 ≤ 6271300599083^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048854569 10000000000 6271300599083 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215187779/400000000 : ℝ), (262723027/500000000 : ℝ), (-2048854569/10000000000 : ℝ)] ![(44403063106213/100000000000000 : ℝ), (43054335678129/100000000000000 : ℝ), (6271300599083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215187779/400000000 : ℝ)|^1083 ≤ (44403063106213/100000000000000 : ℝ)^827
        have hw : |(215187779/400000000 : ℝ)|=(215187779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262723027/500000000 : ℝ)|^1083 ≤ (43054335678129/100000000000000 : ℝ)^827
        have hw : |(262723027/500000000 : ℝ)|=(262723027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048854569/10000000000 : ℝ)|^1083 ≤ (6271300599083/50000000000000 : ℝ)^827
        have hw : |(-2048854569/10000000000 : ℝ)|=(2048854569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_box_15 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1035814301/2500000000 : ℝ)*x 0 + (2205079993/5000000000 : ℝ)*x 1 + (2205080113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035814301/2500000000 : ℝ)^1083 ≤ (3154198948811/10000000000000 : ℝ)^827 := by
    have hnat : (1035814301 : ℕ)^1083*10000000000000^827 ≤ 3154198948811^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035814301 2500000000 3154198948811 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205079993/5000000000 : ℝ)^1083 ≤ (17114502014499/50000000000000 : ℝ)^827 := by
    have hnat : (2205079993 : ℕ)^1083*50000000000000^827 ≤ 17114502014499^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205079993 5000000000 17114502014499 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205080113/5000000000 : ℝ)^1083 ≤ (8557251617087/25000000000000 : ℝ)^827 := by
    have hnat : (2205080113 : ℕ)^1083*25000000000000^827 ≤ 8557251617087^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205080113 5000000000 8557251617087 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035814301/2500000000 : ℝ), (2205079993/5000000000 : ℝ), (2205080113/5000000000 : ℝ)] ![(3154198948811/10000000000000 : ℝ), (17114502014499/50000000000000 : ℝ), (8557251617087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035814301/2500000000 : ℝ)|^1083 ≤ (3154198948811/10000000000000 : ℝ)^827
        have hw : |(1035814301/2500000000 : ℝ)|=(1035814301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205079993/5000000000 : ℝ)|^1083 ≤ (17114502014499/50000000000000 : ℝ)^827
        have hw : |(2205079993/5000000000 : ℝ)|=(2205079993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205080113/5000000000 : ℝ)|^1083 ≤ (8557251617087/25000000000000 : ℝ)^827
        have hw : |(2205080113/5000000000 : ℝ)|=(2205080113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1372_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15717/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59/100 : ℝ) ∧ (2504/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21117/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11219/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (4794667505263727/50000000000000000000 : ℝ) := by
    have hpowers : (11219/100000 : ℝ)^4331 ≤ (4794667505263727/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11219 : ℕ)^4331*50000000000000000000^1024 ≤ 4794667505263727^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11219 100000 4794667505263727 50000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11219/100000 : ℝ)) (X := (4794667505263727/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (4331/1024 : ℝ) ≤ (15144899993082047/50000000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^4331 ≤ (15144899993082047/50000000000000000000 : ℝ)^1024 := by
      have hnat : (589 : ℕ)^4331*50000000000000000000^1024 ≤ 15144899993082047^1024*4000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 15144899993082047 50000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (15144899993082047/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004794667505263727/25000000000000000000 : ℝ) ≤ (10000453417692989/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25004794667505263727/25000000000000000000 : ℝ)^1024 ≤ (10000453417692989/10000000000000000 : ℝ)^4331 := by
      have hnat : (25004794667505263727 : ℕ)^1024*10000000000000000^4331 ≤ 10000453417692989^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004794667505263727 25000000000000000000 10000453417692989 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000453417692989/10000000000000000 : ℝ)) (X := (25004794667505263727/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009969783749172887/25000000000000000000 : ℝ) ≤ (5000471369410223/5000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25009969783749172887/25000000000000000000 : ℝ)^1024 ≤ (5000471369410223/5000000000000000 : ℝ)^4331 := by
      have hnat : (25009969783749172887 : ℕ)^1024*5000000000000000^4331 ≤ 5000471369410223^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009969783749172887 25000000000000000000 5000471369410223 5000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000471369410223/5000000000000000 : ℝ)) (X := (25009969783749172887/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015144899993082047/25000000000000000000 : ℝ) ≤ (10001432059947903/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25015144899993082047/25000000000000000000 : ℝ)^1024 ≤ (10001432059947903/10000000000000000 : ℝ)^4331 := by
      have hnat : (25015144899993082047 : ℕ)^1024*10000000000000000^4331 ≤ 10001432059947903^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015144899993082047 25000000000000000000 10001432059947903 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001432059947903/10000000000000000 : ℝ)) (X := (25015144899993082047/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4794667505263727/50000000000000000000 : ℝ) ≤ ((8762652573743434817/8765000000000000000 : ℝ)+2*(489321127457/350600000000000 : ℝ)*(11219/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (8762652573743434817/8765000000000000000 : ℝ)+2*(489321127457/350600000000000 : ℝ)*(11219/100000 : ℝ)=(10000453417692989/10000000000000000 : ℝ) by norm_num, show 1+2*(4794667505263727/50000000000000000000 : ℝ)=(25004794667505263727/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15144899993082047/50000000000000000000 : ℝ)+(4794667505263727/50000000000000000000 : ℝ) ≤ ((8762652573743434817/8765000000000000000 : ℝ)+(489321127457/350600000000000 : ℝ)*((589/4000 : ℝ)+(11219/100000 : ℝ)))^(4331/1024 : ℝ) := by
    rw [show (8762652573743434817/8765000000000000000 : ℝ)+(489321127457/350600000000000 : ℝ)*((589/4000 : ℝ)+(11219/100000 : ℝ))=(5000471369410223/5000000000000000 : ℝ) by norm_num, show 1+(15144899993082047/50000000000000000000 : ℝ)+(4794667505263727/50000000000000000000 : ℝ)=(25009969783749172887/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15144899993082047/50000000000000000000 : ℝ) ≤ ((8762652573743434817/8765000000000000000 : ℝ)+2*(489321127457/350600000000000 : ℝ)*(589/4000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (8762652573743434817/8765000000000000000 : ℝ)+2*(489321127457/350600000000000 : ℝ)*(589/4000 : ℝ)=(10001432059947903/10000000000000000 : ℝ) by norm_num, show 1+2*(15144899993082047/50000000000000000000 : ℝ)=(25015144899993082047/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8762652573743434817/8765000000000000000 : ℝ)*(X 1 0+X 2 0)+(489321127457/350600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (8762652573743434817/8765000000000000000 : ℝ)) (alpha := (489321127457/350600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8762652573743434817/8765000000000000000 : ℝ)*(X 0 1+X 2 1)+(489321127457/350600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (8762652573743434817/8765000000000000000 : ℝ)) (alpha := (489321127457/350600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8762652573743434817/8765000000000000000 : ℝ)*(X 0 2+X 1 2)+(489321127457/350600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (8762652573743434817/8765000000000000000 : ℝ)) (alpha := (489321127457/350600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1853427603/10000000000 : ℝ)*X 0 0+(5388680581/10000000000 : ℝ)*X 0 1+(5388680437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1057108359/2000000000 : ℝ)*X 1 0+(-997437441/5000000000 : ℝ)*X 1 1+(5388680303/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((264277061/500000000 : ℝ)*X 2 0+(5388680961/10000000000 : ℝ)*X 2 1+(-398974953/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((893267739/2000000000 : ℝ)*X 0 0+(2124455793/5000000000 : ℝ)*X 0 1+(4248911903/10000000000 : ℝ)*X 0 2+(893267739/2000000000 : ℝ)*X 1 0+(2124455793/5000000000 : ℝ)*X 1 1+(4248911903/10000000000 : ℝ)*X 1 2+(893267739/2000000000 : ℝ)*X 2 0+(2124455793/5000000000 : ℝ)*X 2 1+(4248911903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-218598933/1000000000 : ℝ)*X 0 0+(1053110647/2000000000 : ℝ)*X 0 1+(2632776507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342978621/2500000000 : ℝ)*X 1 0+(-1022243939/5000000000 : ℝ)*X 1 1+(658194179/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074383009/2000000000 : ℝ)*X 2 0+(1053110599/2000000000 : ℝ)*X 2 1+(-511121927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((834073549/2000000000 : ℝ)*X 0 0+(879368909/2000000000 : ℝ)*X 0 1+(4396844663/10000000000 : ℝ)*X 0 2+(834073549/2000000000 : ℝ)*X 1 0+(879368909/2000000000 : ℝ)*X 1 1+(4396844663/10000000000 : ℝ)*X 1 2+(834073549/2000000000 : ℝ)*X 2 0+(879368909/2000000000 : ℝ)*X 2 1+(4396844663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1058037957/5000000000 : ℝ)*X 0 0+(5180648967/10000000000 : ℝ)*X 0 1+(675335781/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275712123/10000000000 : ℝ)*X 1 0+(-1989100661/10000000000 : ℝ)*X 1 1+(216107449/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((659463993/1250000000 : ℝ)*X 2 0+(337667861/625000000 : ℝ)*X 2 1+(-397820303/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2249723641/5000000000 : ℝ)*X 0 0+(4232069663/10000000000 : ℝ)*X 0 1+(66126103/156250000 : ℝ)*X 0 2+(2249723641/5000000000 : ℝ)*X 1 0+(4232069663/10000000000 : ℝ)*X 1 1+(66126103/156250000 : ℝ)*X 1 2+(2249723641/5000000000 : ℝ)*X 2 0+(4232069663/10000000000 : ℝ)*X 2 1+(66126103/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-615559/3200000 : ℝ)*X 0 0+(170982673/312500000 : ℝ)*X 0 1+(2627230191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379694133/10000000000 : ℝ)*X 1 0+(-2048854327/10000000000 : ℝ)*X 1 1+(1050892213/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215187779/400000000 : ℝ)*X 2 0+(262723027/500000000 : ℝ)*X 2 1+(-2048854569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1035814301/2500000000 : ℝ)*X 0 0+(2205079993/5000000000 : ℝ)*X 0 1+(2205080113/5000000000 : ℝ)*X 0 2+(1035814301/2500000000 : ℝ)*X 1 0+(2205079993/5000000000 : ℝ)*X 1 1+(2205080113/5000000000 : ℝ)*X 1 2+(1035814301/2500000000 : ℝ)*X 2 0+(2205079993/5000000000 : ℝ)*X 2 1+(2205080113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15717/25000 : ℝ) ≤ (-34438659841052113891380937493133/54781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (607093/100000000000000 : ℝ)*(upper1) + (114457921/100000000000000 : ℝ)*(upper4) + (7787351/5000000000000 : ℝ)*(upper5) + (738535870971283/25000000000000 : ℝ)*(major0) + (738535870971283/25000000000000 : ℝ)*(major1) + (738535870971283/25000000000000 : ℝ)*(major2) + (6182992571/50000000000000 : ℝ)*(sp2) + (698300023/10000000000000 : ℝ)*(sp3) + (2017239522114251/50000000000000 : ℝ)*(sp4) + (1008621086448901/25000000000000 : ℝ)*(sp5) + (4034478493307933/100000000000000 : ℝ)*(sp6) + (947372192657791/50000000000000 : ℝ)*(sp7) + (5907532287/50000000000000 : ℝ)*(sp8) + (651349747/10000000000000 : ℝ)*(sp13) + (473687842078953/25000000000000 : ℝ)*(f.failure) + (161379634371723/4000000000000 : ℝ)*(f.sum) + (838818173749/4382500000000000000000000000 : ℝ)*base66 + (2116567789760885211/219125000000000000000000000000000 : ℝ)*base67 + (2163315082653364789/219125000000000000000000000000000 : ℝ)*base70 + (3235198660402885211/219125000000000000000000000000000 : ℝ)*base71 + (4079570972429/4382500000000000000000000000 : ℝ)*base74 + (2370132438997385211/219125000000000000000000000000000 : ℝ)*base75 + (1756404371229510211/219125000000000000000000000000000 : ℝ)*base77 + (3069105968378760211/219125000000000000000000000000000 : ℝ)*base79 + (7564631126683/2191250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (846149/2500000000000000000000 : ℝ)*base89 + (846149/2500000000000000000000 : ℝ)*base91 + (846149/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59/100 : ℝ) ≤ (258577664911604391940074777/438250000000000000000000000 : ℝ) := by norm_num
    linear_combination (10636099/50000000000000 : ℝ)*(lower1) + (14651851/20000000000000 : ℝ)*(upper2) + (480971/5000000000000 : ℝ)*(lower4) + (3023824086611123/100000000000000 : ℝ)*(major0) + (3023824086611123/100000000000000 : ℝ)*(major1) + (755956021652781/25000000000000 : ℝ)*(major2) + (2044268207439751/50000000000000 : ℝ)*(sp0) + (204424458439311/5000000000000 : ℝ)*(sp1) + (10221312280091/250000000000 : ℝ)*(sp2) + (969721392733229/50000000000000 : ℝ)*(sp3) + (12169803469/100000000000000 : ℝ)*(sp6) + (433052589/50000000000000 : ℝ)*(sp7) + (47913053649/100000000000000 : ℝ)*(sp9) + (41685023/6250000000000 : ℝ)*(sp12) + (484860912892909/25000000000000 : ℝ)*(f.failure) + (4088537081839869/100000000000000 : ℝ)*(f.sum) + (408352239513039/35060000000000000000000000000 : ℝ)*base65 + (6998887163792630509/876500000000000000000000000000000 : ℝ)*base68 + (345215581082655173/219125000000000000000000000000000 : ℝ)*base70 + (7840149729573869491/876500000000000000000000000000000 : ℝ)*base71 + (54038819118739/35060000000000000000000000000 : ℝ)*base73 + (726247220610469827/219125000000000000000000000000000 : ℝ)*base75 + (3492793824570444491/876500000000000000000000000000000 : ℝ)*base77 + (970678497071555509/876500000000000000000000000000000 : ℝ)*base80 + (72604108738131/17530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (10816903/2500000000000000000000 : ℝ)*base90 + (10816903/2500000000000000000000 : ℝ)*base92 + (35816903/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2504/3125 : ℝ) ≤ (351172575334395404742394536583809/438250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406997539/100000000000000 : ℝ)*(upper0) + (33607617/25000000000000 : ℝ)*(upper2) + (561314047/100000000000000 : ℝ)*(lower5) + (333460000687187/10000000000000 : ℝ)*(major0) + (333460000687187/10000000000000 : ℝ)*(major1) + (3334600006871871/100000000000000 : ℝ)*(major2) + (27373197439/50000000000000 : ℝ)*(sp1) + (42813670623/100000000000000 : ℝ)*(sp3) + (855677197/20000000000000 : ℝ)*(sp4) + (4503712092886997/100000000000000 : ℝ)*(sp8) + (450366353851411/10000000000000 : ℝ)*(sp9) + (4503718284908987/100000000000000 : ℝ)*(sp10) + (2138728698367439/100000000000000 : ℝ)*(sp11) + (382727201/20000000000000 : ℝ)*(sp12) + (1069385756019031/50000000000000 : ℝ)*(f.failure) + (4503718284908987/100000000000000 : ℝ)*(f.sum) + (66468158589363/35060000000000000000000000000 : ℝ)*base66 + (237914675399142721/87650000000000000000000000000000 : ℝ)*base68 + (10173353594029582607/876500000000000000000000000000000 : ℝ)*base69 + (379515508235757279/87650000000000000000000000000000 : ℝ)*base71 + (638440221620103/35060000000000000000000000000 : ℝ)*base74 + (2389557805287582607/876500000000000000000000000000000 : ℝ)*base75 + (650676922588914779/87650000000000000000000000000000 : ℝ)*base77 + (682751428958514779/87650000000000000000000000000000 : ℝ)*base79 + (1045652164997/1753000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7996923/5000000000000000000000 : ℝ)*base89 + (7996923/5000000000000000000000 : ℝ)*base91 + (42003077/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21117/25000 : ℝ) ≤ (-11567849582016947875125282287757/13695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (175303771/100000000000000 : ℝ)*(lower0) + (108103659/50000000000000 : ℝ)*(lower1) + (4678927/4000000000000 : ℝ)*(lower2) + (27688107/20000000000000 : ℝ)*(lower4) + (105357499469643/3125000000000 : ℝ)*(major0) + (105357499469643/3125000000000 : ℝ)*(major1) + (105357499469643/3125000000000 : ℝ)*(major2) + (695870099/3125000000000 : ℝ)*(sp0) + (180589643959/100000000000000 : ℝ)*(sp5) + (410794975967/100000000000000 : ℝ)*(sp6) + (576076591314327/12500000000000 : ℝ)*(sp12) + (144014200272307/3125000000000 : ℝ)*(sp13) + (576028025422727/12500000000000 : ℝ)*(sp14) + (27030002756657/1250000000000 : ℝ)*(sp15) + (27030002756657/1250000000000 : ℝ)*(f.failure) + (4608634998357783/100000000000000 : ℝ)*(f.sum) + (15945869418947/1095625000000000000000000000 : ℝ)*base65 + (263463532613464669/27390625000000000000000000000000 : ℝ)*base68 + (348111173457714669/27390625000000000000000000000000 : ℝ)*base70 + (1328371672118847831/27390625000000000000000000000000 : ℝ)*base71 + (455329043767/4382500000000000000000000000 : ℝ)*base74 + (103680854807089669/27390625000000000000000000000000 : ℝ)*base76 + (3500934353879267/855957031250000000000000000000 : ℝ)*base78 + (89251180585353603/13695312500000000000000000000000 : ℝ)*base79 + (5916870245921/2191250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1487981/125000000000000000000 : ℝ)*base89 + (1487981/125000000000000000000 : ℝ)*base91 + (1487981/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1372_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15717/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59/100 : ℝ) else (2504/3125 : ℝ) ≤ X j i ∧ X j i ≤ (21117/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1372_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1372_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15717/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59/100 : ℝ) else (2504/3125 : ℝ) ≤ X j i ∧ X j i ≤ (21117/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1372_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15717/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59/100 : ℝ) else (2504/3125 : ℝ) ≤ X j i ∧ X j i ≤ (21117/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
