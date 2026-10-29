-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:43.411635+00:00
-- url     : https://prove2.me/submissions/1a3dc44a-4fcc-4ade-987d-d7e25aa6a499

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
theorem support_rectangle_w1372_s3_0 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016857471/10000000000 : ℝ)*x 0 + (3389679/6250000 : ℝ)*x 1 + (5234128021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016857471/10000000000 : ℝ)^1083 ≤ (491468403817/4000000000000 : ℝ)^827 := by
    have hnat : (2016857471 : ℕ)^1083*4000000000000^827 ≤ 491468403817^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016857471 10000000000 491468403817 4000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3389679/6250000 : ℝ)^1083 ≤ (44876997373563/100000000000000 : ℝ)^827 := by
    have hnat : (3389679 : ℕ)^1083*100000000000000^827 ≤ 44876997373563^827*6250000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389679 6250000 44876997373563 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234128021/10000000000 : ℝ)^1083 ≤ (5354536564321/12500000000000 : ℝ)^827 := by
    have hnat : (5234128021 : ℕ)^1083*12500000000000^827 ≤ 5354536564321^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234128021 10000000000 5354536564321 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016857471/10000000000 : ℝ), (3389679/6250000 : ℝ), (5234128021/10000000000 : ℝ)] ![(491468403817/4000000000000 : ℝ), (44876997373563/100000000000000 : ℝ), (5354536564321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016857471/10000000000 : ℝ)|^1083 ≤ (491468403817/4000000000000 : ℝ)^827
        have hw : |(-2016857471/10000000000 : ℝ)|=(2016857471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3389679/6250000 : ℝ)|^1083 ≤ (44876997373563/100000000000000 : ℝ)^827
        have hw : |(3389679/6250000 : ℝ)|=(3389679/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234128021/10000000000 : ℝ)|^1083 ≤ (5354536564321/12500000000000 : ℝ)^827
        have hw : |(5234128021/10000000000 : ℝ)|=(5234128021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s3_1 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2675808871/5000000000 : ℝ)*x 0 + (-1056781687/5000000000 : ℝ)*x 1 + (2617064049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675808871/5000000000 : ℝ)^1083 ≤ (44099832203519/100000000000000 : ℝ)^827 := by
    have hnat : (2675808871 : ℕ)^1083*100000000000000^827 ≤ 44099832203519^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675808871 5000000000 44099832203519 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056781687/5000000000 : ℝ)^1083 ≤ (6531937222963/50000000000000 : ℝ)^827 := by
    have hnat : (1056781687 : ℕ)^1083*50000000000000^827 ≤ 6531937222963^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056781687 5000000000 6531937222963 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617064049/5000000000 : ℝ)^1083 ≤ (4283629333981/10000000000000 : ℝ)^827 := by
    have hnat : (2617064049 : ℕ)^1083*10000000000000^827 ≤ 4283629333981^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617064049 5000000000 4283629333981 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675808871/5000000000 : ℝ), (-1056781687/5000000000 : ℝ), (2617064049/5000000000 : ℝ)] ![(44099832203519/100000000000000 : ℝ), (6531937222963/50000000000000 : ℝ), (4283629333981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675808871/5000000000 : ℝ)|^1083 ≤ (44099832203519/100000000000000 : ℝ)^827
        have hw : |(2675808871/5000000000 : ℝ)|=(2675808871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056781687/5000000000 : ℝ)|^1083 ≤ (6531937222963/50000000000000 : ℝ)^827
        have hw : |(-1056781687/5000000000 : ℝ)|=(1056781687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617064049/5000000000 : ℝ)|^1083 ≤ (4283629333981/10000000000000 : ℝ)^827
        have hw : |(2617064049/5000000000 : ℝ)|=(2617064049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s3_2 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337904441/2500000000 : ℝ)*x 0 + (1308532001/2500000000 : ℝ)*x 1 + (-2113563469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337904441/2500000000 : ℝ)^1083 ≤ (1378119763779/3125000000000 : ℝ)^827 := by
    have hnat : (1337904441 : ℕ)^1083*3125000000000^827 ≤ 1378119763779^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337904441 2500000000 1378119763779 3125000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308532001/2500000000 : ℝ)^1083 ≤ (10709073083093/25000000000000 : ℝ)^827 := by
    have hnat : (1308532001 : ℕ)^1083*25000000000000^827 ≤ 10709073083093^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308532001 2500000000 10709073083093 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113563469/10000000000 : ℝ)^1083 ≤ (2612775042977/20000000000000 : ℝ)^827 := by
    have hnat : (2113563469 : ℕ)^1083*20000000000000^827 ≤ 2612775042977^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113563469 10000000000 2612775042977 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337904441/2500000000 : ℝ), (1308532001/2500000000 : ℝ), (-2113563469/10000000000 : ℝ)] ![(1378119763779/3125000000000 : ℝ), (10709073083093/25000000000000 : ℝ), (2612775042977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337904441/2500000000 : ℝ)|^1083 ≤ (1378119763779/3125000000000 : ℝ)^827
        have hw : |(1337904441/2500000000 : ℝ)|=(1337904441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308532001/2500000000 : ℝ)|^1083 ≤ (10709073083093/25000000000000 : ℝ)^827
        have hw : |(1308532001/2500000000 : ℝ)|=(1308532001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113563469/10000000000 : ℝ)|^1083 ≤ (2612775042977/20000000000000 : ℝ)^827
        have hw : |(-2113563469/10000000000 : ℝ)|=(2113563469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s3_3 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4317939571/10000000000 : ℝ)*x 0 + (4121679571/10000000000 : ℝ)*x 1 + (1130696427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317939571/10000000000 : ℝ)^1083 ≤ (16647363994471/50000000000000 : ℝ)^827 := by
    have hnat : (4317939571 : ℕ)^1083*50000000000000^827 ≤ 16647363994471^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317939571 10000000000 16647363994471 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4121679571/10000000000 : ℝ)^1083 ≤ (15663523243301/50000000000000 : ℝ)^827 := by
    have hnat : (4121679571 : ℕ)^1083*50000000000000^827 ≤ 15663523243301^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121679571 10000000000 15663523243301 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130696427/2500000000 : ℝ)^1083 ≤ (4422278189771/12500000000000 : ℝ)^827 := by
    have hnat : (1130696427 : ℕ)^1083*12500000000000^827 ≤ 4422278189771^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130696427 2500000000 4422278189771 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317939571/10000000000 : ℝ), (4121679571/10000000000 : ℝ), (1130696427/2500000000 : ℝ)] ![(16647363994471/50000000000000 : ℝ), (15663523243301/50000000000000 : ℝ), (4422278189771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317939571/10000000000 : ℝ)|^1083 ≤ (16647363994471/50000000000000 : ℝ)^827
        have hw : |(4317939571/10000000000 : ℝ)|=(4317939571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4121679571/10000000000 : ℝ)|^1083 ≤ (15663523243301/50000000000000 : ℝ)^827
        have hw : |(4121679571/10000000000 : ℝ)|=(4121679571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130696427/2500000000 : ℝ)|^1083 ≤ (4422278189771/12500000000000 : ℝ)^827
        have hw : |(1130696427/2500000000 : ℝ)|=(1130696427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s3_4 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-504218797/2500000000 : ℝ)*x 0 + (65436301/125000000 : ℝ)*x 1 + (5422705753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504218797/2500000000 : ℝ)^1083 ≤ (12286851438367/100000000000000 : ℝ)^827 := by
    have hnat : (504218797 : ℕ)^1083*100000000000000^827 ≤ 12286851438367^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504218797 2500000000 12286851438367 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65436301/125000000 : ℝ)^1083 ≤ (42844610060113/100000000000000 : ℝ)^827 := by
    have hnat : (65436301 : ℕ)^1083*100000000000000^827 ≤ 42844610060113^827*125000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65436301 125000000 42844610060113 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422705753/10000000000 : ℝ)^1083 ≤ (44868538486971/100000000000000 : ℝ)^827 := by
    have hnat : (5422705753 : ℕ)^1083*100000000000000^827 ≤ 44868538486971^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422705753 10000000000 44868538486971 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504218797/2500000000 : ℝ), (65436301/125000000 : ℝ), (5422705753/10000000000 : ℝ)] ![(12286851438367/100000000000000 : ℝ), (42844610060113/100000000000000 : ℝ), (44868538486971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504218797/2500000000 : ℝ)|^1083 ≤ (12286851438367/100000000000000 : ℝ)^827
        have hw : |(-504218797/2500000000 : ℝ)|=(504218797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65436301/125000000 : ℝ)|^1083 ≤ (42844610060113/100000000000000 : ℝ)^827
        have hw : |(65436301/125000000 : ℝ)|=(65436301/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422705753/10000000000 : ℝ)|^1083 ≤ (44868538486971/100000000000000 : ℝ)^827
        have hw : |(5422705753/10000000000 : ℝ)|=(5422705753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s3_5 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5302678699/10000000000 : ℝ)*x 0 + (-1924985643/10000000000 : ℝ)*x 1 + (677838219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302678699/10000000000 : ℝ)^1083 ≤ (2178623206071/5000000000000 : ℝ)^827 := by
    have hnat : (5302678699 : ℕ)^1083*5000000000000^827 ≤ 2178623206071^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302678699 10000000000 2178623206071 5000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1924985643/10000000000 : ℝ)^1083 ≤ (11558997384963/100000000000000 : ℝ)^827 := by
    have hnat : (1924985643 : ℕ)^1083*100000000000000^827 ≤ 11558997384963^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924985643 10000000000 11558997384963 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677838219/1250000000 : ℝ)^1083 ≤ (5608567309517/12500000000000 : ℝ)^827 := by
    have hnat : (677838219 : ℕ)^1083*12500000000000^827 ≤ 5608567309517^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677838219 1250000000 5608567309517 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302678699/10000000000 : ℝ), (-1924985643/10000000000 : ℝ), (677838219/1250000000 : ℝ)] ![(2178623206071/5000000000000 : ℝ), (11558997384963/100000000000000 : ℝ), (5608567309517/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302678699/10000000000 : ℝ)|^1083 ≤ (2178623206071/5000000000000 : ℝ)^827
        have hw : |(5302678699/10000000000 : ℝ)|=(5302678699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1924985643/10000000000 : ℝ)|^1083 ≤ (11558997384963/100000000000000 : ℝ)^827
        have hw : |(-1924985643/10000000000 : ℝ)|=(1924985643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677838219/1250000000 : ℝ)|^1083 ≤ (5608567309517/12500000000000 : ℝ)^827
        have hw : |(677838219/1250000000 : ℝ)|=(677838219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s3_6 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5302678631/10000000000 : ℝ)*x 0 + (5422705807/10000000000 : ℝ)*x 1 + (-96249283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302678631/10000000000 : ℝ)^1083 ≤ (43572463389693/100000000000000 : ℝ)^827 := by
    have hnat : (5302678631 : ℕ)^1083*100000000000000^827 ≤ 43572463389693^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302678631 10000000000 43572463389693 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422705807/10000000000 : ℝ)^1083 ≤ (5608567384011/12500000000000 : ℝ)^827 := by
    have hnat : (5422705807 : ℕ)^1083*12500000000000^827 ≤ 5608567384011^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422705807 10000000000 5608567384011 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96249283/500000000 : ℝ)^1083 ≤ (11558997518643/100000000000000 : ℝ)^827 := by
    have hnat : (96249283 : ℕ)^1083*100000000000000^827 ≤ 11558997518643^827*500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96249283 500000000 11558997518643 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302678631/10000000000 : ℝ), (5422705807/10000000000 : ℝ), (-96249283/500000000 : ℝ)] ![(43572463389693/100000000000000 : ℝ), (5608567384011/12500000000000 : ℝ), (11558997518643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302678631/10000000000 : ℝ)|^1083 ≤ (43572463389693/100000000000000 : ℝ)^827
        have hw : |(5302678631/10000000000 : ℝ)|=(5302678631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422705807/10000000000 : ℝ)|^1083 ≤ (5608567384011/12500000000000 : ℝ)^827
        have hw : |(5422705807/10000000000 : ℝ)|=(5422705807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96249283/500000000 : ℝ)|^1083 ≤ (11558997518643/100000000000000 : ℝ)^827
        have hw : |(-96249283/500000000 : ℝ)|=(96249283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s3_7 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (539747131/1250000000 : ℝ)*x 0 + (90422837/200000000 : ℝ)*x 1 + (128854161/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539747131/1250000000 : ℝ)^1083 ≤ (16647553210213/50000000000000 : ℝ)^827 := by
    have hnat : (539747131 : ℕ)^1083*50000000000000^827 ≤ 16647553210213^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539747131 1250000000 16647553210213 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90422837/200000000 : ℝ)^1083 ≤ (35361387427357/100000000000000 : ℝ)^827 := by
    have hnat : (90422837 : ℕ)^1083*100000000000000^827 ≤ 35361387427357^827*200000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90422837 200000000 35361387427357 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128854161/312500000 : ℝ)^1083 ≤ (31343506137151/100000000000000 : ℝ)^827 := by
    have hnat : (128854161 : ℕ)^1083*100000000000000^827 ≤ 31343506137151^827*312500000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128854161 312500000 31343506137151 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539747131/1250000000 : ℝ), (90422837/200000000 : ℝ), (128854161/312500000 : ℝ)] ![(16647553210213/50000000000000 : ℝ), (35361387427357/100000000000000 : ℝ), (31343506137151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539747131/1250000000 : ℝ)|^1083 ≤ (16647553210213/50000000000000 : ℝ)^827
        have hw : |(539747131/1250000000 : ℝ)|=(539747131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90422837/200000000 : ℝ)|^1083 ≤ (35361387427357/100000000000000 : ℝ)^827
        have hw : |(90422837/200000000 : ℝ)|=(90422837/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128854161/312500000 : ℝ)|^1083 ≤ (31343506137151/100000000000000 : ℝ)^827
        have hw : |(128854161/312500000 : ℝ)|=(128854161/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1372_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1599/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (439/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14983/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1599/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5021/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1599/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5021/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1599/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5021/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1599/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5021/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1599/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5021/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1599/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5021/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5021/50000 : ℝ) ^ (4331/1024 : ℝ) ≤ (3000381027374691/50000000000000000000 : ℝ) := by
    have hpowers : (5021/50000 : ℝ)^4331 ≤ (3000381027374691/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5021 : ℕ)^4331*50000000000000000000^1024 ≤ 3000381027374691^1024*50000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5021 50000 3000381027374691 50000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5021/50000 : ℝ)) (X := (3000381027374691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1599/10000 : ℝ) ^ (4331/1024 : ℝ) ≤ (42922330803528421/100000000000000000000 : ℝ) := by
    have hpowers : (1599/10000 : ℝ)^4331 ≤ (42922330803528421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1599 : ℕ)^4331*100000000000000000000^1024 ≤ 42922330803528421^1024*10000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1599 10000 42922330803528421 100000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1599/10000 : ℝ)) (X := (42922330803528421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003000381027374691/25000000000000000000 : ℝ) ≤ (2500070936259661/2500000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25003000381027374691/25000000000000000000 : ℝ)^1024 ≤ (2500070936259661/2500000000000000 : ℝ)^4331 := by
      have hnat : (25003000381027374691 : ℕ)^1024*2500000000000000^4331 ≤ 2500070936259661^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003000381027374691 25000000000000000000 2500070936259661 2500000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070936259661/2500000000000000 : ℝ)) (X := (25003000381027374691/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048923092858277803/100000000000000000000 : ℝ) ≤ (10001156497174393/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (100048923092858277803/100000000000000000000 : ℝ)^1024 ≤ (10001156497174393/10000000000000000 : ℝ)^4331 := by
      have hnat : (100048923092858277803 : ℕ)^1024*10000000000000000^4331 ≤ 10001156497174393^4331*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048923092858277803 100000000000000000000 10001156497174393 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001156497174393/10000000000000000 : ℝ)) (X := (100048923092858277803/100000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042922330803528421/50000000000000000000 : ℝ) ≤ (5001014624655071/5000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (50042922330803528421/50000000000000000000 : ℝ)^1024 ≤ (5001014624655071/5000000000000000 : ℝ)^4331 := by
      have hnat : (50042922330803528421 : ℕ)^1024*5000000000000000^4331 ≤ 5001014624655071^4331*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042922330803528421 50000000000000000000 5001014624655071 5000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001014624655071/5000000000000000 : ℝ)) (X := (50042922330803528421/50000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3000381027374691/50000000000000000000 : ℝ) ≤ ((14866039840398867899/14870000000000000000 : ℝ)+2*(872752135749/594800000000000 : ℝ)*(5021/50000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (14866039840398867899/14870000000000000000 : ℝ)+2*(872752135749/594800000000000 : ℝ)*(5021/50000 : ℝ)=(2500070936259661/2500000000000000 : ℝ) by norm_num, show 1+2*(3000381027374691/50000000000000000000 : ℝ)=(25003000381027374691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42922330803528421/100000000000000000000 : ℝ)+(3000381027374691/50000000000000000000 : ℝ) ≤ ((14866039840398867899/14870000000000000000 : ℝ)+(872752135749/594800000000000 : ℝ)*((1599/10000 : ℝ)+(5021/50000 : ℝ)))^(4331/1024 : ℝ) := by
    rw [show (14866039840398867899/14870000000000000000 : ℝ)+(872752135749/594800000000000 : ℝ)*((1599/10000 : ℝ)+(5021/50000 : ℝ))=(10001156497174393/10000000000000000 : ℝ) by norm_num, show 1+(42922330803528421/100000000000000000000 : ℝ)+(3000381027374691/50000000000000000000 : ℝ)=(100048923092858277803/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42922330803528421/100000000000000000000 : ℝ) ≤ ((14866039840398867899/14870000000000000000 : ℝ)+2*(872752135749/594800000000000 : ℝ)*(1599/10000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (14866039840398867899/14870000000000000000 : ℝ)+2*(872752135749/594800000000000 : ℝ)*(1599/10000 : ℝ)=(5001014624655071/5000000000000000 : ℝ) by norm_num, show 1+2*(42922330803528421/100000000000000000000 : ℝ)=(50042922330803528421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14866039840398867899/14870000000000000000 : ℝ)*(X 1 0+X 2 0)+(872752135749/594800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (5021/50000 : ℝ)) (hi := (1599/10000 : ℝ)) (c := (14866039840398867899/14870000000000000000 : ℝ)) (alpha := (872752135749/594800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14866039840398867899/14870000000000000000 : ℝ)*(X 0 1+X 2 1)+(872752135749/594800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (5021/50000 : ℝ)) (hi := (1599/10000 : ℝ)) (c := (14866039840398867899/14870000000000000000 : ℝ)) (alpha := (872752135749/594800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14866039840398867899/14870000000000000000 : ℝ)*(X 0 2+X 1 2)+(872752135749/594800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (5021/50000 : ℝ)) (hi := (1599/10000 : ℝ)) (c := (14866039840398867899/14870000000000000000 : ℝ)) (alpha := (872752135749/594800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2016857471/10000000000 : ℝ)*X 0 0+(3389679/6250000 : ℝ)*X 0 1+(5234128021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675808871/5000000000 : ℝ)*X 1 0+(-1056781687/5000000000 : ℝ)*X 1 1+(2617064049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337904441/2500000000 : ℝ)*X 2 0+(1308532001/2500000000 : ℝ)*X 2 1+(-2113563469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317939571/10000000000 : ℝ)*X 0 0+(4121679571/10000000000 : ℝ)*X 0 1+(1130696427/2500000000 : ℝ)*X 0 2+(4317939571/10000000000 : ℝ)*X 1 0+(4121679571/10000000000 : ℝ)*X 1 1+(1130696427/2500000000 : ℝ)*X 1 2+(4317939571/10000000000 : ℝ)*X 2 0+(4121679571/10000000000 : ℝ)*X 2 1+(1130696427/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-504218797/2500000000 : ℝ)*X 0 0+(65436301/125000000 : ℝ)*X 0 1+(5422705753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302678699/10000000000 : ℝ)*X 1 0+(-1924985643/10000000000 : ℝ)*X 1 1+(677838219/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302678631/10000000000 : ℝ)*X 2 0+(5422705807/10000000000 : ℝ)*X 2 1+(-96249283/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539747131/1250000000 : ℝ)*X 0 0+(90422837/200000000 : ℝ)*X 0 1+(128854161/312500000 : ℝ)*X 0 2+(539747131/1250000000 : ℝ)*X 1 0+(90422837/200000000 : ℝ)*X 1 1+(128854161/312500000 : ℝ)*X 1 2+(539747131/1250000000 : ℝ)*X 2 0+(90422837/200000000 : ℝ)*X 2 1+(128854161/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (848865759784780335533683149/92937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12846889/781250000000 : ℝ)*(base19) + (378696493/25000000000000 : ℝ)*(base23) + (40491873/50000000000000 : ℝ)*(lower2) + (7408989/2500000000000 : ℝ)*(upper3) + (81090133/100000000000000 : ℝ)*(upper5) + (3887093623080221/100000000000000 : ℝ)*(major0) + (3887093623080221/100000000000000 : ℝ)*(major1) + (1943546811540111/50000000000000 : ℝ)*(major2) + (2640512403382139/50000000000000 : ℝ)*(sp0) + (5281051161711703/100000000000000 : ℝ)*(sp1) + (5281051291327523/100000000000000 : ℝ)*(sp2) + (124655906995081/5000000000000 : ℝ)*(sp3) + (27999349217/100000000000000 : ℝ)*(sp4) + (3199137549/20000000000000 : ℝ)*(sp7) + (1246567067794683/50000000000000 : ℝ)*(f.failure) + (1056210561222699/20000000000000 : ℝ)*(f.sum) + (474069656400727/59480000000000000000000000000 : ℝ)*base65 + (18239155978855675679/1487000000000000000000000000000000 : ℝ)*base67 + (9930716540138909289/743500000000000000000000000000000 : ℝ)*base69 + (11119164176343675679/1487000000000000000000000000000000 : ℝ)*base71 + (96232812117767/59480000000000000000000000000 : ℝ)*base73 + (17853339784646409289/743500000000000000000000000000000 : ℝ)*base75 + (25424465545247950679/1487000000000000000000000000000000 : ℝ)*base77 + (22212416161377950679/1487000000000000000000000000000000 : ℝ)*base79 + (155156090627909/29740000000000000000000000000 : ℝ)*base81 + (23652239/5000000000000000000000 : ℝ)*base89 + (23652239/5000000000000000000000 : ℝ)*base91 + (26347761/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1470082339022547604649314593/371750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181589793/25000000000000 : ℝ)*(base19) + (14420671/2000000000000 : ℝ)*(base23) + (73853939/100000000000000 : ℝ)*(upper3) + (6657277/20000000000000 : ℝ)*(lower4) + (44470081/50000000000000 : ℝ)*(upper5) + (3919268079423931/100000000000000 : ℝ)*(major0) + (3919268079423931/100000000000000 : ℝ)*(major1) + (3919268079423931/100000000000000 : ℝ)*(major2) + (54744461/400000000000 : ℝ)*(sp1) + (13706116863/100000000000000 : ℝ)*(sp2) + (5324765590086183/100000000000000 : ℝ)*(sp4) + (5324751177611761/100000000000000 : ℝ)*(sp5) + (532475116293577/10000000000000 : ℝ)*(sp6) + (2513770436945279/100000000000000 : ℝ)*(sp7) + (2513770436945279/100000000000000 : ℝ)*(f.failure) + (5324765590086183/100000000000000 : ℝ)*(f.sum) + (183369665106199/29740000000000000000000000000 : ℝ)*base65 + (20693999209991265969/1487000000000000000000000000000000 : ℝ)*base67 + (2723087600912265969/1487000000000000000000000000000000 : ℝ)*base69 + (2652008073024265969/1487000000000000000000000000000000 : ℝ)*base71 + (44442337984339/29740000000000000000000000000 : ℝ)*base73 + (5445884270061265969/1487000000000000000000000000000000 : ℝ)*base75 + (10693792158443265969/1487000000000000000000000000000000 : ℝ)*base77 + (1512295517382734031/1487000000000000000000000000000000 : ℝ)*base80 + (16878469279179/29740000000000000000000000000 : ℝ)*base81 + (35885693/10000000000000000000000 : ℝ)*base90 + (35885693/10000000000000000000000 : ℝ)*base92 + (35885693/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1372_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1599/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14983/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1372_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1372_s4_0 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2018097111/10000000000 : ℝ)*x 0 + (676653233/1250000000 : ℝ)*x 1 + (2621786767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2018097111/10000000000 : ℝ)^1083 ≤ (12296600640779/100000000000000 : ℝ)^827 := by
    have hnat : (2018097111 : ℕ)^1083*100000000000000^827 ≤ 12296600640779^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018097111 10000000000 12296600640779 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676653233/1250000000 : ℝ)^1083 ≤ (44765846984091/100000000000000 : ℝ)^827 := by
    have hnat : (676653233 : ℕ)^1083*100000000000000^827 ≤ 44765846984091^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676653233 1250000000 44765846984091 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621786767/5000000000 : ℝ)^1083 ≤ (21468776180827/50000000000000 : ℝ)^827 := by
    have hnat : (2621786767 : ℕ)^1083*50000000000000^827 ≤ 21468776180827^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621786767 5000000000 21468776180827 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2018097111/10000000000 : ℝ), (676653233/1250000000 : ℝ), (2621786767/5000000000 : ℝ)] ![(12296600640779/100000000000000 : ℝ), (44765846984091/100000000000000 : ℝ), (21468776180827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2018097111/10000000000 : ℝ)|^1083 ≤ (12296600640779/100000000000000 : ℝ)^827
        have hw : |(-2018097111/10000000000 : ℝ)|=(2018097111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676653233/1250000000 : ℝ)|^1083 ≤ (44765846984091/100000000000000 : ℝ)^827
        have hw : |(676653233/1250000000 : ℝ)|=(676653233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621786767/5000000000 : ℝ)|^1083 ≤ (21468776180827/50000000000000 : ℝ)^827
        have hw : |(2621786767/5000000000 : ℝ)|=(2621786767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s4_1 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668623763/1250000000 : ℝ)*x 0 + (-2104550537/10000000000 : ℝ)*x 1 + (16386167/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668623763/1250000000 : ℝ)^1083 ≤ (8814295732251/20000000000000 : ℝ)^827 := by
    have hnat : (668623763 : ℕ)^1083*20000000000000^827 ≤ 8814295732251^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668623763 1250000000 8814295732251 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104550537/10000000000 : ℝ)^1083 ≤ (811935623341/6250000000000 : ℝ)^827 := by
    have hnat : (2104550537 : ℕ)^1083*6250000000000^827 ≤ 811935623341^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104550537 10000000000 811935623341 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16386167/31250000 : ℝ)^1083 ≤ (42937551353653/100000000000000 : ℝ)^827 := by
    have hnat : (16386167 : ℕ)^1083*100000000000000^827 ≤ 42937551353653^827*31250000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16386167 31250000 42937551353653 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668623763/1250000000 : ℝ), (-2104550537/10000000000 : ℝ), (16386167/31250000 : ℝ)] ![(8814295732251/20000000000000 : ℝ), (811935623341/6250000000000 : ℝ), (42937551353653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668623763/1250000000 : ℝ)|^1083 ≤ (8814295732251/20000000000000 : ℝ)^827
        have hw : |(668623763/1250000000 : ℝ)|=(668623763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104550537/10000000000 : ℝ)|^1083 ≤ (811935623341/6250000000000 : ℝ)^827
        have hw : |(-2104550537/10000000000 : ℝ)|=(2104550537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16386167/31250000 : ℝ)|^1083 ≤ (42937551353653/100000000000000 : ℝ)^827
        have hw : |(16386167/31250000 : ℝ)|=(16386167/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s4_2 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348990073/10000000000 : ℝ)*x 0 + (5243573617/10000000000 : ℝ)*x 1 + (-263068793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348990073/10000000000 : ℝ)^1083 ≤ (22035739163387/50000000000000 : ℝ)^827 := by
    have hnat : (5348990073 : ℕ)^1083*50000000000000^827 ≤ 22035739163387^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348990073 10000000000 22035739163387 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243573617/10000000000 : ℝ)^1083 ≤ (42937553251697/100000000000000 : ℝ)^827 := by
    have hnat : (5243573617 : ℕ)^1083*100000000000000^827 ≤ 42937553251697^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243573617 10000000000 42937553251697 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263068793/1250000000 : ℝ)^1083 ≤ (324774210333/2500000000000 : ℝ)^827 := by
    have hnat : (263068793 : ℕ)^1083*2500000000000^827 ≤ 324774210333^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263068793 1250000000 324774210333 2500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348990073/10000000000 : ℝ), (5243573617/10000000000 : ℝ), (-263068793/1250000000 : ℝ)] ![(22035739163387/50000000000000 : ℝ), (42937553251697/100000000000000 : ℝ), (324774210333/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348990073/10000000000 : ℝ)|^1083 ≤ (22035739163387/50000000000000 : ℝ)^827
        have hw : |(5348990073/10000000000 : ℝ)|=(5348990073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243573617/10000000000 : ℝ)|^1083 ≤ (42937553251697/100000000000000 : ℝ)^827
        have hw : |(5243573617/10000000000 : ℝ)|=(5243573617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263068793/1250000000 : ℝ)|^1083 ≤ (324774210333/2500000000000 : ℝ)^827
        have hw : |(-263068793/1250000000 : ℝ)|=(263068793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s4_3 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1079673303/2500000000 : ℝ)*x 0 + (258903643/625000000 : ℝ)*x 1 + (4501822103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079673303/2500000000 : ℝ)^1083 ≤ (266418705797/800000000000 : ℝ)^827 := by
    have hnat : (1079673303 : ℕ)^1083*800000000000^827 ≤ 266418705797^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079673303 2500000000 266418705797 800000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258903643/625000000 : ℝ)^1083 ≤ (31534024992221/100000000000000 : ℝ)^827 := by
    have hnat : (258903643 : ℕ)^1083*100000000000000^827 ≤ 31534024992221^827*625000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258903643 625000000 31534024992221 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501822103/10000000000 : ℝ)^1083 ≤ (7032727354629/20000000000000 : ℝ)^827 := by
    have hnat : (4501822103 : ℕ)^1083*20000000000000^827 ≤ 7032727354629^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501822103 10000000000 7032727354629 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079673303/2500000000 : ℝ), (258903643/625000000 : ℝ), (4501822103/10000000000 : ℝ)] ![(266418705797/800000000000 : ℝ), (31534024992221/100000000000000 : ℝ), (7032727354629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079673303/2500000000 : ℝ)|^1083 ≤ (266418705797/800000000000 : ℝ)^827
        have hw : |(1079673303/2500000000 : ℝ)|=(1079673303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258903643/625000000 : ℝ)|^1083 ≤ (31534024992221/100000000000000 : ℝ)^827
        have hw : |(258903643/625000000 : ℝ)|=(258903643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501822103/10000000000 : ℝ)|^1083 ≤ (7032727354629/20000000000000 : ℝ)^827
        have hw : |(4501822103/10000000000 : ℝ)|=(4501822103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s4_4 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2018109857/10000000000 : ℝ)*x 0 + (524419687/1000000000 : ℝ)*x 1 + (1353149807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2018109857/10000000000 : ℝ)^1083 ≤ (3074175586327/25000000000000 : ℝ)^827 := by
    have hnat : (2018109857 : ℕ)^1083*25000000000000^827 ≤ 3074175586327^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018109857 10000000000 3074175586327 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524419687/1000000000 : ℝ)^1083 ≤ (2684014798217/6250000000000 : ℝ)^827 := by
    have hnat : (524419687 : ℕ)^1083*6250000000000^827 ≤ 2684014798217^827*1000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524419687 1000000000 2684014798217 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353149807/2500000000 : ℝ)^1083 ≤ (1118976521747/2500000000000 : ℝ)^827 := by
    have hnat : (1353149807 : ℕ)^1083*2500000000000^827 ≤ 1118976521747^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353149807 2500000000 1118976521747 2500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2018109857/10000000000 : ℝ), (524419687/1000000000 : ℝ), (1353149807/2500000000 : ℝ)] ![(3074175586327/25000000000000 : ℝ), (2684014798217/6250000000000 : ℝ), (1118976521747/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2018109857/10000000000 : ℝ)|^1083 ≤ (3074175586327/25000000000000 : ℝ)^827
        have hw : |(-2018109857/10000000000 : ℝ)|=(2018109857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524419687/1000000000 : ℝ)|^1083 ≤ (2684014798217/6250000000000 : ℝ)^827
        have hw : |(524419687/1000000000 : ℝ)|=(524419687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353149807/2500000000 : ℝ)|^1083 ≤ (1118976521747/2500000000000 : ℝ)^827
        have hw : |(1353149807/2500000000 : ℝ)|=(1353149807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s4_5 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (331571519/625000000 : ℝ)*x 0 + (-1935524997/10000000000 : ℝ)*x 1 + (2706299513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331571519/625000000 : ℝ)^1083 ≤ (5449874702421/12500000000000 : ℝ)^827 := by
    have hnat : (331571519 : ℕ)^1083*12500000000000^827 ≤ 5449874702421^827*625000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331571519 625000000 5449874702421 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935524997/10000000000 : ℝ)^1083 ≤ (2910485921087/25000000000000 : ℝ)^827 := by
    have hnat : (1935524997 : ℕ)^1083*25000000000000^827 ≤ 2910485921087^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935524997 10000000000 2910485921087 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706299513/5000000000 : ℝ)^1083 ≤ (44759058682373/100000000000000 : ℝ)^827 := by
    have hnat : (2706299513 : ℕ)^1083*100000000000000^827 ≤ 44759058682373^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706299513 5000000000 44759058682373 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331571519/625000000 : ℝ), (-1935524997/10000000000 : ℝ), (2706299513/5000000000 : ℝ)] ![(5449874702421/12500000000000 : ℝ), (2910485921087/25000000000000 : ℝ), (44759058682373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331571519/625000000 : ℝ)|^1083 ≤ (5449874702421/12500000000000 : ℝ)^827
        have hw : |(331571519/625000000 : ℝ)|=(331571519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1935524997/10000000000 : ℝ)|^1083 ≤ (2910485921087/25000000000000 : ℝ)^827
        have hw : |(-1935524997/10000000000 : ℝ)|=(1935524997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706299513/5000000000 : ℝ)|^1083 ≤ (44759058682373/100000000000000 : ℝ)^827
        have hw : |(2706299513/5000000000 : ℝ)|=(2706299513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s4_6 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305144427/10000000000 : ℝ)*x 0 + (5412598913/10000000000 : ℝ)*x 1 + (-241940623/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305144427/10000000000 : ℝ)^1083 ≤ (43598998943123/100000000000000 : ℝ)^827 := by
    have hnat : (5305144427 : ℕ)^1083*100000000000000^827 ≤ 43598998943123^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305144427 10000000000 43598998943123 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412598913/10000000000 : ℝ)^1083 ≤ (44759057458669/100000000000000 : ℝ)^827 := by
    have hnat : (5412598913 : ℕ)^1083*100000000000000^827 ≤ 44759057458669^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412598913 10000000000 44759057458669 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241940623/1250000000 : ℝ)^1083 ≤ (232838871639/2000000000000 : ℝ)^827 := by
    have hnat : (241940623 : ℕ)^1083*2000000000000^827 ≤ 232838871639^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241940623 1250000000 232838871639 2000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305144427/10000000000 : ℝ), (5412598913/10000000000 : ℝ), (-241940623/1250000000 : ℝ)] ![(43598998943123/100000000000000 : ℝ), (44759057458669/100000000000000 : ℝ), (232838871639/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305144427/10000000000 : ℝ)|^1083 ≤ (43598998943123/100000000000000 : ℝ)^827
        have hw : |(5305144427/10000000000 : ℝ)|=(5305144427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412598913/10000000000 : ℝ)|^1083 ≤ (44759057458669/100000000000000 : ℝ)^827
        have hw : |(5412598913/10000000000 : ℝ)|=(5412598913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-241940623/1250000000 : ℝ)|^1083 ≤ (232838871639/2000000000000 : ℝ)^827
        have hw : |(-241940623/1250000000 : ℝ)|=(241940623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s4_7 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4318719849/10000000000 : ℝ)*x 0 + (2250250981/5000000000 : ℝ)*x 1 + (1035946439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318719849/10000000000 : ℝ)^1083 ≤ (33302607211473/100000000000000 : ℝ)^827 := by
    have hnat : (4318719849 : ℕ)^1083*100000000000000^827 ≤ 33302607211473^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318719849 10000000000 33302607211473 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250250981/5000000000 : ℝ)^1083 ≤ (2196883363267/6250000000000 : ℝ)^827 := by
    have hnat : (2250250981 : ℕ)^1083*6250000000000^827 ≤ 2196883363267^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250250981 5000000000 2196883363267 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035946439/2500000000 : ℝ)^1083 ≤ (3943407368997/12500000000000 : ℝ)^827 := by
    have hnat : (1035946439 : ℕ)^1083*12500000000000^827 ≤ 3943407368997^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035946439 2500000000 3943407368997 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318719849/10000000000 : ℝ), (2250250981/5000000000 : ℝ), (1035946439/2500000000 : ℝ)] ![(33302607211473/100000000000000 : ℝ), (2196883363267/6250000000000 : ℝ), (3943407368997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318719849/10000000000 : ℝ)|^1083 ≤ (33302607211473/100000000000000 : ℝ)^827
        have hw : |(4318719849/10000000000 : ℝ)|=(4318719849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250250981/5000000000 : ℝ)|^1083 ≤ (2196883363267/6250000000000 : ℝ)^827
        have hw : |(2250250981/5000000000 : ℝ)|=(2250250981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035946439/2500000000 : ℝ)|^1083 ≤ (3943407368997/12500000000000 : ℝ)^827
        have hw : |(1035946439/2500000000 : ℝ)|=(1035946439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1372_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11177/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (439/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (439/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (439/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (439/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (439/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (439/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (439/4000 : ℝ) ^ (4331/1024 : ℝ) ≤ (4368863301991951/50000000000000000000 : ℝ) := by
    have hpowers : (439/4000 : ℝ)^4331 ≤ (4368863301991951/50000000000000000000 : ℝ)^1024 := by
      have hnat : (439 : ℕ)^4331*50000000000000000000^1024 ≤ 4368863301991951^1024*4000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 4000 4368863301991951 50000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/4000 : ℝ)) (X := (4368863301991951/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14983/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (32598789876737041/100000000000000000000 : ℝ) := by
    have hpowers : (14983/100000 : ℝ)^4331 ≤ (32598789876737041/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14983 : ℕ)^4331*100000000000000000000^1024 ≤ 32598789876737041^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14983 100000 32598789876737041 100000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14983/100000 : ℝ)) (X := (32598789876737041/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004368863301991951/25000000000000000000 : ℝ) ≤ (10000413153320113/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25004368863301991951/25000000000000000000 : ℝ)^1024 ≤ (10000413153320113/10000000000000000 : ℝ)^4331 := by
      have hnat : (25004368863301991951 : ℕ)^1024*10000000000000000^4331 ≤ 10000413153320113^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004368863301991951 25000000000000000000 10000413153320113 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000413153320113/10000000000000000 : ℝ)) (X := (25004368863301991951/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041336516480720943/100000000000000000000 : ℝ) ≤ (10000977185739723/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (100041336516480720943/100000000000000000000 : ℝ)^1024 ≤ (10000977185739723/10000000000000000 : ℝ)^4331 := by
      have hnat : (100041336516480720943 : ℕ)^1024*10000000000000000^4331 ≤ 10000977185739723^4331*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041336516480720943 100000000000000000000 10000977185739723 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000977185739723/10000000000000000 : ℝ)) (X := (100041336516480720943/100000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032598789876737041/50000000000000000000 : ℝ) ≤ (10001541218159333/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (50032598789876737041/50000000000000000000 : ℝ)^1024 ≤ (10001541218159333/10000000000000000 : ℝ)^4331 := by
      have hnat : (50032598789876737041 : ℕ)^1024*10000000000000000^4331 ≤ 10001541218159333^4331*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032598789876737041 50000000000000000000 10001541218159333 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001541218159333/10000000000000000 : ℝ)) (X := (50032598789876737041/50000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4368863301991951/50000000000000000000 : ℝ) ≤ ((10017318851724143351/10020000000000000000 : ℝ)+2*(56403241961/40080000000000 : ℝ)*(439/4000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (10017318851724143351/10020000000000000000 : ℝ)+2*(56403241961/40080000000000 : ℝ)*(439/4000 : ℝ)=(10000413153320113/10000000000000000 : ℝ) by norm_num, show 1+2*(4368863301991951/50000000000000000000 : ℝ)=(25004368863301991951/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32598789876737041/100000000000000000000 : ℝ)+(4368863301991951/50000000000000000000 : ℝ) ≤ ((10017318851724143351/10020000000000000000 : ℝ)+(56403241961/40080000000000 : ℝ)*((14983/100000 : ℝ)+(439/4000 : ℝ)))^(4331/1024 : ℝ) := by
    rw [show (10017318851724143351/10020000000000000000 : ℝ)+(56403241961/40080000000000 : ℝ)*((14983/100000 : ℝ)+(439/4000 : ℝ))=(10000977185739723/10000000000000000 : ℝ) by norm_num, show 1+(32598789876737041/100000000000000000000 : ℝ)+(4368863301991951/50000000000000000000 : ℝ)=(100041336516480720943/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32598789876737041/100000000000000000000 : ℝ) ≤ ((10017318851724143351/10020000000000000000 : ℝ)+2*(56403241961/40080000000000 : ℝ)*(14983/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (10017318851724143351/10020000000000000000 : ℝ)+2*(56403241961/40080000000000 : ℝ)*(14983/100000 : ℝ)=(10001541218159333/10000000000000000 : ℝ) by norm_num, show 1+2*(32598789876737041/100000000000000000000 : ℝ)=(50032598789876737041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10017318851724143351/10020000000000000000 : ℝ)*(X 1 0+X 2 0)+(56403241961/40080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (439/4000 : ℝ)) (hi := (14983/100000 : ℝ)) (c := (10017318851724143351/10020000000000000000 : ℝ)) (alpha := (56403241961/40080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10017318851724143351/10020000000000000000 : ℝ)*(X 0 1+X 2 1)+(56403241961/40080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (439/4000 : ℝ)) (hi := (14983/100000 : ℝ)) (c := (10017318851724143351/10020000000000000000 : ℝ)) (alpha := (56403241961/40080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10017318851724143351/10020000000000000000 : ℝ)*(X 0 2+X 1 2)+(56403241961/40080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (439/4000 : ℝ)) (hi := (14983/100000 : ℝ)) (c := (10017318851724143351/10020000000000000000 : ℝ)) (alpha := (56403241961/40080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2018097111/10000000000 : ℝ)*X 0 0+(676653233/1250000000 : ℝ)*X 0 1+(2621786767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668623763/1250000000 : ℝ)*X 1 0+(-2104550537/10000000000 : ℝ)*X 1 1+(16386167/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348990073/10000000000 : ℝ)*X 2 0+(5243573617/10000000000 : ℝ)*X 2 1+(-263068793/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079673303/2500000000 : ℝ)*X 0 0+(258903643/625000000 : ℝ)*X 0 1+(4501822103/10000000000 : ℝ)*X 0 2+(1079673303/2500000000 : ℝ)*X 1 0+(258903643/625000000 : ℝ)*X 1 1+(4501822103/10000000000 : ℝ)*X 1 2+(1079673303/2500000000 : ℝ)*X 2 0+(258903643/625000000 : ℝ)*X 2 1+(4501822103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2018109857/10000000000 : ℝ)*X 0 0+(524419687/1000000000 : ℝ)*X 0 1+(1353149807/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331571519/625000000 : ℝ)*X 1 0+(-1935524997/10000000000 : ℝ)*X 1 1+(2706299513/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305144427/10000000000 : ℝ)*X 2 0+(5412598913/10000000000 : ℝ)*X 2 1+(-241940623/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318719849/10000000000 : ℝ)*X 0 0+(2250250981/5000000000 : ℝ)*X 0 1+(1035946439/2500000000 : ℝ)*X 0 2+(4318719849/10000000000 : ℝ)*X 1 0+(2250250981/5000000000 : ℝ)*X 1 1+(1035946439/2500000000 : ℝ)*X 1 2+(4318719849/10000000000 : ℝ)*X 2 0+(2250250981/5000000000 : ℝ)*X 2 1+(1035946439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (976122359268412864142106649/167000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (604382881/50000000000000 : ℝ)*(base19) + (140026691/12500000000000 : ℝ)*(base23) + (14546839/50000000000000 : ℝ)*(lower2) + (15047/200000000000 : ℝ)*(upper3) + (98173777/50000000000000 : ℝ)*(upper5) + (4338589381893189/100000000000000 : ℝ)*(major0) + (4338589381893189/100000000000000 : ℝ)*(major1) + (433858938189319/10000000000000 : ℝ)*(major2) + (184200946999943/3125000000000 : ℝ)*(sp0) + (2947229693512577/50000000000000 : ℝ)*(sp1) + (5894459475577389/100000000000000 : ℝ)*(sp2) + (695676976137279/25000000000000 : ℝ)*(sp3) + (1514589637/5000000000000 : ℝ)*(sp4) + (10068611533/100000000000000 : ℝ)*(sp7) + (55654359463213/2000000000000 : ℝ)*(f.failure) + (5894460595790917/100000000000000 : ℝ)*(f.sum) + (455630840557/160320000000000000000000000 : ℝ)*base66 + (6142144311968036339/1002000000000000000000000000000000 : ℝ)*base67 + (79776384203792969/100200000000000000000000000000000 : ℝ)*base69 + (7614259687245963661/1002000000000000000000000000000000 : ℝ)*base72 + (14344268077571/4008000000000000000000000000 : ℝ)*base73 + (1201171592392592969/100200000000000000000000000000000 : ℝ)*base75 + (4199154081832737887/334000000000000000000000000000000 : ℝ)*base78 + (1321833814606737887/334000000000000000000000000000000 : ℝ)*base80 + (1296476502897/668000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3220729/200000000000000000000 : ℝ)*base89 + (3220729/200000000000000000000 : ℝ)*base91 + (1220729/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87157404522186980596855427/10437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1325524937/100000000000000 : ℝ)*(base19) + (316553659/20000000000000 : ℝ)*(base23) + (27808577/50000000000000 : ℝ)*(upper2) + (81963357/100000000000000 : ℝ)*(upper3) + (64405963/50000000000000 : ℝ)*(upper5) + (273172167446659/6250000000000 : ℝ)*(major0) + (273172167446659/6250000000000 : ℝ)*(major1) + (273172167446659/6250000000000 : ℝ)*(major2) + (24029334533/100000000000000 : ℝ)*(sp1) + (25811762997/100000000000000 : ℝ)*(sp2) + (5938160679957641/100000000000000 : ℝ)*(sp4) + (5938135325098171/100000000000000 : ℝ)*(sp5) + (5938133285426349/100000000000000 : ℝ)*(sp6) + (1401674199994219/50000000000000 : ℝ)*(sp7) + (1401674199994219/50000000000000 : ℝ)*(f.failure) + (5938160679957641/100000000000000 : ℝ)*(f.sum) + (3258633567829/501000000000000000000000000 : ℝ)*base66 + (1069053083666485691/62625000000000000000000000000000 : ℝ)*base68 + (126095385697735691/62625000000000000000000000000000 : ℝ)*base70 + (591552253947985691/62625000000000000000000000000000 : ℝ)*base72 + (620834282863/125250000000000000000000000 : ℝ)*base74 + (694309784799985691/62625000000000000000000000000000 : ℝ)*base76 + (619990666496485691/62625000000000000000000000000000 : ℝ)*base78 + (568067181555985691/62625000000000000000000000000000 : ℝ)*base80 + (78583749113/125250000000000000000000000 : ℝ)*base81 + (73115327/5000000000000000000000 : ℝ)*base89 + (73115327/5000000000000000000000 : ℝ)*base91 + (73115327/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1372_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (439/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1372_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1372_s5_0 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2018298393/10000000000 : ℝ)*x 0 + (2705728849/5000000000 : ℝ)*x 1 + (5245209269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2018298393/10000000000 : ℝ)^1083 ≤ (12298206759329/100000000000000 : ℝ)^827 := by
    have hnat : (2018298393 : ℕ)^1083*100000000000000^827 ≤ 12298206759329^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018298393 10000000000 12298206759329 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705728849/5000000000 : ℝ)^1083 ≤ (5593337421163/12500000000000 : ℝ)^827 := by
    have hnat : (2705728849 : ℕ)^1083*12500000000000^827 ≤ 5593337421163^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705728849 5000000000 5593337421163 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245209269/10000000000 : ℝ)^1083 ≤ (21477546931913/50000000000000 : ℝ)^827 := by
    have hnat : (5245209269 : ℕ)^1083*50000000000000^827 ≤ 21477546931913^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245209269 10000000000 21477546931913 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2018298393/10000000000 : ℝ), (2705728849/5000000000 : ℝ), (5245209269/10000000000 : ℝ)] ![(12298206759329/100000000000000 : ℝ), (5593337421163/12500000000000 : ℝ), (21477546931913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2018298393/10000000000 : ℝ)|^1083 ≤ (12298206759329/100000000000000 : ℝ)^827
        have hw : |(-2018298393/10000000000 : ℝ)|=(2018298393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705728849/5000000000 : ℝ)|^1083 ≤ (5593337421163/12500000000000 : ℝ)^827
        have hw : |(2705728849/5000000000 : ℝ)|=(2705728849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245209269/10000000000 : ℝ)|^1083 ≤ (21477546931913/50000000000000 : ℝ)^827
        have hw : |(5245209269/10000000000 : ℝ)|=(5245209269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s5_1 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674268393/5000000000 : ℝ)*x 0 + (-2102985341/10000000000 : ℝ)*x 1 + (5245209227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674268393/5000000000 : ℝ)^1083 ≤ (4406658756689/10000000000000 : ℝ)^827 := by
    have hnat : (2674268393 : ℕ)^1083*10000000000000^827 ≤ 4406658756689^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674268393 5000000000 4406658756689 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2102985341/10000000000 : ℝ)^1083 ≤ (6489159500747/50000000000000 : ℝ)^827 := by
    have hnat : (2102985341 : ℕ)^1083*50000000000000^827 ≤ 6489159500747^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102985341 10000000000 6489159500747 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245209227/10000000000 : ℝ)^1083 ≤ (42955093413399/100000000000000 : ℝ)^827 := by
    have hnat : (5245209227 : ℕ)^1083*100000000000000^827 ≤ 42955093413399^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245209227 10000000000 42955093413399 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674268393/5000000000 : ℝ), (-2102985341/10000000000 : ℝ), (5245209227/10000000000 : ℝ)] ![(4406658756689/10000000000000 : ℝ), (6489159500747/50000000000000 : ℝ), (42955093413399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674268393/5000000000 : ℝ)|^1083 ≤ (4406658756689/10000000000000 : ℝ)^827
        have hw : |(2674268393/5000000000 : ℝ)|=(2674268393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2102985341/10000000000 : ℝ)|^1083 ≤ (6489159500747/50000000000000 : ℝ)^827
        have hw : |(-2102985341/10000000000 : ℝ)|=(2102985341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245209227/10000000000 : ℝ)|^1083 ≤ (42955093413399/100000000000000 : ℝ)^827
        have hw : |(5245209227/10000000000 : ℝ)|=(5245209227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s5_2 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348536861/10000000000 : ℝ)*x 0 + (1049041851/2000000000 : ℝ)*x 1 + (-525746301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348536861/10000000000 : ℝ)^1083 ≤ (8813317675219/20000000000000 : ℝ)^827 := by
    have hnat : (5348536861 : ℕ)^1083*20000000000000^827 ≤ 8813317675219^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348536861 10000000000 8813317675219 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049041851/2000000000 : ℝ)^1083 ≤ (10738773428421/25000000000000 : ℝ)^827 := by
    have hnat : (1049041851 : ℕ)^1083*25000000000000^827 ≤ 10738773428421^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049041851 2000000000 10738773428421 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525746301/2500000000 : ℝ)^1083 ≤ (2595663578859/20000000000000 : ℝ)^827 := by
    have hnat : (525746301 : ℕ)^1083*20000000000000^827 ≤ 2595663578859^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525746301 2500000000 2595663578859 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348536861/10000000000 : ℝ), (1049041851/2000000000 : ℝ), (-525746301/2500000000 : ℝ)] ![(8813317675219/20000000000000 : ℝ), (10738773428421/25000000000000 : ℝ), (2595663578859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348536861/10000000000 : ℝ)|^1083 ≤ (8813317675219/20000000000000 : ℝ)^827
        have hw : |(5348536861/10000000000 : ℝ)|=(5348536861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049041851/2000000000 : ℝ)|^1083 ≤ (10738773428421/25000000000000 : ℝ)^827
        have hw : |(1049041851/2000000000 : ℝ)|=(1049041851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525746301/2500000000 : ℝ)|^1083 ≤ (2595663578859/20000000000000 : ℝ)^827
        have hw : |(-525746301/2500000000 : ℝ)|=(525746301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s5_3 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4318814911/10000000000 : ℝ)*x 0 + (165841949/400000000 : ℝ)*x 1 + (4498201883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318814911/10000000000 : ℝ)^1083 ≤ (16651783587327/50000000000000 : ℝ)^827 := by
    have hnat : (4318814911 : ℕ)^1083*50000000000000^827 ≤ 16651783587327^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318814911 10000000000 16651783587327 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165841949/400000000 : ℝ)^1083 ≤ (31569822250627/100000000000000 : ℝ)^827 := by
    have hnat : (165841949 : ℕ)^1083*100000000000000^827 ≤ 31569822250627^827*400000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165841949 400000000 31569822250627 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498201883/10000000000 : ℝ)^1083 ≤ (35126610559881/100000000000000 : ℝ)^827 := by
    have hnat : (4498201883 : ℕ)^1083*100000000000000^827 ≤ 35126610559881^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498201883 10000000000 35126610559881 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318814911/10000000000 : ℝ), (165841949/400000000 : ℝ), (4498201883/10000000000 : ℝ)] ![(16651783587327/50000000000000 : ℝ), (31569822250627/100000000000000 : ℝ), (35126610559881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318814911/10000000000 : ℝ)|^1083 ≤ (16651783587327/50000000000000 : ℝ)^827
        have hw : |(4318814911/10000000000 : ℝ)|=(4318814911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165841949/400000000 : ℝ)|^1083 ≤ (31569822250627/100000000000000 : ℝ)^827
        have hw : |(165841949/400000000 : ℝ)|=(165841949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498201883/10000000000 : ℝ)|^1083 ≤ (35126610559881/100000000000000 : ℝ)^827
        have hw : |(4498201883/10000000000 : ℝ)|=(4498201883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s5_4 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2018310439/10000000000 : ℝ)*x 0 + (163931501/312500000 : ℝ)*x 1 + (338178487/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2018310439/10000000000 : ℝ)^1083 ≤ (1229830288129/10000000000000 : ℝ)^827 := by
    have hnat : (2018310439 : ℕ)^1083*10000000000000^827 ≤ 1229830288129^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018310439 10000000000 1229830288129 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163931501/312500000 : ℝ)^1083 ≤ (42961515377743/100000000000000 : ℝ)^827 := by
    have hnat : (163931501 : ℕ)^1083*100000000000000^827 ≤ 42961515377743^827*312500000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163931501 312500000 42961515377743 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338178487/625000000 : ℝ)^1083 ≤ (22370090860807/50000000000000 : ℝ)^827 := by
    have hnat : (338178487 : ℕ)^1083*50000000000000^827 ≤ 22370090860807^827*625000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338178487 625000000 22370090860807 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2018310439/10000000000 : ℝ), (163931501/312500000 : ℝ), (338178487/625000000 : ℝ)] ![(1229830288129/10000000000000 : ℝ), (42961515377743/100000000000000 : ℝ), (22370090860807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2018310439/10000000000 : ℝ)|^1083 ≤ (1229830288129/10000000000000 : ℝ)^827
        have hw : |(-2018310439/10000000000 : ℝ)|=(2018310439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163931501/312500000 : ℝ)|^1083 ≤ (42961515377743/100000000000000 : ℝ)^827
        have hw : |(163931501/312500000 : ℝ)|=(163931501/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338178487/625000000 : ℝ)|^1083 ≤ (22370090860807/50000000000000 : ℝ)^827
        have hw : |(338178487/625000000 : ℝ)|=(338178487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s5_5 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305570617/10000000000 : ℝ)*x 0 + (-121083673/625000000 : ℝ)*x 1 + (1352713949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305570617/10000000000 : ℝ)^1083 ≤ (43603585754789/100000000000000 : ℝ)^827 := by
    have hnat : (5305570617 : ℕ)^1083*100000000000000^827 ≤ 43603585754789^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305570617 10000000000 43603585754789 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121083673/625000000 : ℝ)^1083 ≤ (11656232462139/100000000000000 : ℝ)^827 := by
    have hnat : (121083673 : ℕ)^1083*100000000000000^827 ≤ 11656232462139^827*625000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121083673 625000000 11656232462139 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352713949/2500000000 : ℝ)^1083 ≤ (22370090882463/50000000000000 : ℝ)^827 := by
    have hnat : (1352713949 : ℕ)^1083*50000000000000^827 ≤ 22370090882463^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352713949 2500000000 22370090882463 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305570617/10000000000 : ℝ), (-121083673/625000000 : ℝ), (1352713949/2500000000 : ℝ)] ![(43603585754789/100000000000000 : ℝ), (11656232462139/100000000000000 : ℝ), (22370090882463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305570617/10000000000 : ℝ)|^1083 ≤ (43603585754789/100000000000000 : ℝ)^827
        have hw : |(5305570617/10000000000 : ℝ)|=(5305570617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121083673/625000000 : ℝ)|^1083 ≤ (11656232462139/100000000000000 : ℝ)^827
        have hw : |(-121083673/625000000 : ℝ)|=(121083673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352713949/2500000000 : ℝ)|^1083 ≤ (22370090882463/50000000000000 : ℝ)^827
        have hw : |(1352713949/2500000000 : ℝ)|=(1352713949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s5_6 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652785309/5000000000 : ℝ)*x 0 + (5410855793/10000000000 : ℝ)*x 1 + (-1937338771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652785309/5000000000 : ℝ)^1083 ≤ (43603585765551/100000000000000 : ℝ)^827 := by
    have hnat : (2652785309 : ℕ)^1083*100000000000000^827 ≤ 43603585765551^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652785309 5000000000 43603585765551 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410855793/10000000000 : ℝ)^1083 ≤ (22370090866221/50000000000000 : ℝ)^827 := by
    have hnat : (5410855793 : ℕ)^1083*50000000000000^827 ≤ 22370090866221^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410855793 10000000000 22370090866221 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1937338771/10000000000 : ℝ)^1083 ≤ (728514530361/6250000000000 : ℝ)^827 := by
    have hnat : (1937338771 : ℕ)^1083*6250000000000^827 ≤ 728514530361^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937338771 10000000000 728514530361 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652785309/5000000000 : ℝ), (5410855793/10000000000 : ℝ), (-1937338771/10000000000 : ℝ)] ![(43603585765551/100000000000000 : ℝ), (22370090866221/50000000000000 : ℝ), (728514530361/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652785309/5000000000 : ℝ)|^1083 ≤ (43603585765551/100000000000000 : ℝ)^827
        have hw : |(2652785309/5000000000 : ℝ)|=(2652785309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410855793/10000000000 : ℝ)|^1083 ≤ (22370090866221/50000000000000 : ℝ)^827
        have hw : |(5410855793/10000000000 : ℝ)|=(5410855793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1937338771/10000000000 : ℝ)|^1083 ≤ (728514530361/6250000000000 : ℝ)^827
        have hw : |(-1937338771/10000000000 : ℝ)|=(1937338771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s5_7 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2159420261/5000000000 : ℝ)*x 0 + (1124233439/2500000000 : ℝ)*x 1 + (4147323207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159420261/5000000000 : ℝ)^1083 ≤ (33303825802953/100000000000000 : ℝ)^827 := by
    have hnat : (2159420261 : ℕ)^1083*100000000000000^827 ≤ 33303825802953^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159420261 5000000000 33303825802953 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124233439/2500000000 : ℝ)^1083 ≤ (35113642827257/100000000000000 : ℝ)^827 := by
    have hnat : (1124233439 : ℕ)^1083*100000000000000^827 ≤ 35113642827257^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124233439 2500000000 35113642827257 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147323207/10000000000 : ℝ)^1083 ≤ (7895632839501/25000000000000 : ℝ)^827 := by
    have hnat : (4147323207 : ℕ)^1083*25000000000000^827 ≤ 7895632839501^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147323207 10000000000 7895632839501 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159420261/5000000000 : ℝ), (1124233439/2500000000 : ℝ), (4147323207/10000000000 : ℝ)] ![(33303825802953/100000000000000 : ℝ), (35113642827257/100000000000000 : ℝ), (7895632839501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159420261/5000000000 : ℝ)|^1083 ≤ (33303825802953/100000000000000 : ℝ)^827
        have hw : |(2159420261/5000000000 : ℝ)|=(2159420261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124233439/2500000000 : ℝ)|^1083 ≤ (35113642827257/100000000000000 : ℝ)^827
        have hw : |(1124233439/2500000000 : ℝ)|=(1124233439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147323207/10000000000 : ℝ)|^1083 ≤ (7895632839501/25000000000000 : ℝ)^827
        have hw : |(4147323207/10000000000 : ℝ)|=(4147323207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1372_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2803/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3683/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11177/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (9438415320438653/100000000000000000000 : ℝ) := by
    have hpowers : (11177/100000 : ℝ)^4331 ≤ (9438415320438653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11177 : ℕ)^4331*100000000000000000000^1024 ≤ 9438415320438653^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11177 100000 9438415320438653 100000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11177/100000 : ℝ)) (X := (9438415320438653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (30674460044664871/100000000000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^4331 ≤ (30674460044664871/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14769 : ℕ)^4331*100000000000000000000^1024 ≤ 30674460044664871^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 30674460044664871 100000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (30674460044664871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009438415320438653/50000000000000000000 : ℝ) ≤ (2500111570547547/2500000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (50009438415320438653/50000000000000000000 : ℝ)^1024 ≤ (2500111570547547/2500000000000000 : ℝ)^4331 := by
      have hnat : (50009438415320438653 : ℕ)^1024*2500000000000000^4331 ≤ 2500111570547547^4331*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009438415320438653 50000000000000000000 2500111570547547 2500000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111570547547/2500000000000000 : ℝ)) (X := (50009438415320438653/50000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010028218841275881/25000000000000000000 : ℝ) ≤ (2500237065893443/2500000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25010028218841275881/25000000000000000000 : ℝ)^1024 ≤ (2500237065893443/2500000000000000 : ℝ)^4331 := by
      have hnat : (25010028218841275881 : ℕ)^1024*2500000000000000^4331 ≤ 2500237065893443^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010028218841275881 25000000000000000000 2500237065893443 2500000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500237065893443/2500000000000000 : ℝ)) (X := (25010028218841275881/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030674460044664871/50000000000000000000 : ℝ) ≤ (2500362561239339/2500000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (50030674460044664871/50000000000000000000 : ℝ)^1024 ≤ (2500362561239339/2500000000000000 : ℝ)^4331 := by
      have hnat : (50030674460044664871 : ℕ)^1024*2500000000000000^4331 ≤ 2500362561239339^4331*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030674460044664871 50000000000000000000 2500362561239339 2500000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500362561239339/2500000000000000 : ℝ)) (X := (50030674460044664871/50000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9438415320438653/100000000000000000000 : ℝ) ≤ ((224439885961115741/224500000000000000 : ℝ)+2*(15686918237/11225000000000 : ℝ)*(11177/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (224439885961115741/224500000000000000 : ℝ)+2*(15686918237/11225000000000 : ℝ)*(11177/100000 : ℝ)=(2500111570547547/2500000000000000 : ℝ) by norm_num, show 1+2*(9438415320438653/100000000000000000000 : ℝ)=(50009438415320438653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30674460044664871/100000000000000000000 : ℝ)+(9438415320438653/100000000000000000000 : ℝ) ≤ ((224439885961115741/224500000000000000 : ℝ)+(15686918237/11225000000000 : ℝ)*((14769/100000 : ℝ)+(11177/100000 : ℝ)))^(4331/1024 : ℝ) := by
    rw [show (224439885961115741/224500000000000000 : ℝ)+(15686918237/11225000000000 : ℝ)*((14769/100000 : ℝ)+(11177/100000 : ℝ))=(2500237065893443/2500000000000000 : ℝ) by norm_num, show 1+(30674460044664871/100000000000000000000 : ℝ)+(9438415320438653/100000000000000000000 : ℝ)=(25010028218841275881/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30674460044664871/100000000000000000000 : ℝ) ≤ ((224439885961115741/224500000000000000 : ℝ)+2*(15686918237/11225000000000 : ℝ)*(14769/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (224439885961115741/224500000000000000 : ℝ)+2*(15686918237/11225000000000 : ℝ)*(14769/100000 : ℝ)=(2500362561239339/2500000000000000 : ℝ) by norm_num, show 1+2*(30674460044664871/100000000000000000000 : ℝ)=(50030674460044664871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (224439885961115741/224500000000000000 : ℝ)*(X 1 0+X 2 0)+(15686918237/11225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (224439885961115741/224500000000000000 : ℝ)) (alpha := (15686918237/11225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (224439885961115741/224500000000000000 : ℝ)*(X 0 1+X 2 1)+(15686918237/11225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (224439885961115741/224500000000000000 : ℝ)) (alpha := (15686918237/11225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (224439885961115741/224500000000000000 : ℝ)*(X 0 2+X 1 2)+(15686918237/11225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (11177/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (224439885961115741/224500000000000000 : ℝ)) (alpha := (15686918237/11225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2018298393/10000000000 : ℝ)*X 0 0+(2705728849/5000000000 : ℝ)*X 0 1+(5245209269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674268393/5000000000 : ℝ)*X 1 0+(-2102985341/10000000000 : ℝ)*X 1 1+(5245209227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348536861/10000000000 : ℝ)*X 2 0+(1049041851/2000000000 : ℝ)*X 2 1+(-525746301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318814911/10000000000 : ℝ)*X 0 0+(165841949/400000000 : ℝ)*X 0 1+(4498201883/10000000000 : ℝ)*X 0 2+(4318814911/10000000000 : ℝ)*X 1 0+(165841949/400000000 : ℝ)*X 1 1+(4498201883/10000000000 : ℝ)*X 1 2+(4318814911/10000000000 : ℝ)*X 2 0+(165841949/400000000 : ℝ)*X 2 1+(4498201883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2018310439/10000000000 : ℝ)*X 0 0+(163931501/312500000 : ℝ)*X 0 1+(338178487/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305570617/10000000000 : ℝ)*X 1 0+(-121083673/625000000 : ℝ)*X 1 1+(1352713949/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652785309/5000000000 : ℝ)*X 2 0+(5410855793/10000000000 : ℝ)*X 2 1+(-1937338771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159420261/5000000000 : ℝ)*X 0 0+(1124233439/2500000000 : ℝ)*X 0 1+(4147323207/10000000000 : ℝ)*X 0 2+(2159420261/5000000000 : ℝ)*X 1 0+(1124233439/2500000000 : ℝ)*X 1 1+(4147323207/10000000000 : ℝ)*X 1 2+(2159420261/5000000000 : ℝ)*X 2 0+(1124233439/2500000000 : ℝ)*X 2 1+(4147323207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7649926585183695549352149/1403125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (848467027/100000000000000 : ℝ)*(base19) + (465566823/50000000000000 : ℝ)*(base23) + (220909/3125000000000 : ℝ)*(lower2) + (16008813/12500000000000 : ℝ)*(upper5) + (1106853170261513/25000000000000 : ℝ)*(major0) + (1106853170261513/25000000000000 : ℝ)*(major1) + (4427412681046053/100000000000000 : ℝ)*(major2) + (6015112767768039/100000000000000 : ℝ)*(sp0) + (6015134748923037/100000000000000 : ℝ)*(sp1) + (751892012786977/12500000000000 : ℝ)*(sp2) + (1419840776046091/50000000000000 : ℝ)*(sp3) + (12132830711/50000000000000 : ℝ)*(sp4) + (359009849/25000000000000 : ℝ)*(sp5) + (3297417501/50000000000000 : ℝ)*(sp7) + (177480509182949/6250000000000 : ℝ)*(f.failure) + (6015137033429461/100000000000000 : ℝ)*(f.sum) + (492066450273/89800000000000000000000000 : ℝ)*base65 + (14496534969068867/5612500000000000000000000000000 : ℝ)*base68 + (172157440405049727/22450000000000000000000000000000 : ℝ)*base70 + (42832319223168867/5612500000000000000000000000000 : ℝ)*base72 + (1303546855621/449000000000000000000000000 : ℝ)*base73 + (129305831439950273/22450000000000000000000000000000 : ℝ)*base75 + (26369072761078867/5612500000000000000000000000000 : ℝ)*base78 + (186238453159578867/5612500000000000000000000000000 : ℝ)*base80 + (3009850803/280625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (4230417/625000000000000000000 : ℝ)*base89 + (4230417/625000000000000000000 : ℝ)*base91 + (2019583/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11257163200384424887464447/1403125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276837147/20000000000000 : ℝ)*(base19) + (1497654911/100000000000000 : ℝ)*(base23) + (41234207/25000000000000 : ℝ)*(upper3) + (6406121/12500000000000 : ℝ)*(lower4) + (33065773/20000000000000 : ℝ)*(upper5) + (278724272808793/6250000000000 : ℝ)*(major0) + (278724272808793/6250000000000 : ℝ)*(major1) + (278724272808793/6250000000000 : ℝ)*(major2) + (14268617533/50000000000000 : ℝ)*(sp1) + (30479878339/100000000000000 : ℝ)*(sp2) + (94669550419241/1562500000000 : ℝ)*(sp4) + (3029410652705311/50000000000000 : ℝ)*(sp5) + (242352769971927/4000000000000 : ℝ)*(sp6) + (2860325235619193/100000000000000 : ℝ)*(sp7) + (2860325235619193/100000000000000 : ℝ)*(f.failure) + (94669550419241/1562500000000 : ℝ)*(f.sum) + (252653248113/1122500000000000000000000000 : ℝ)*base66 + (3518470401443113/1403125000000000000000000000000 : ℝ)*base67 + (1690872647491869/701562500000000000000000000000 : ℝ)*base69 + (3934926432443113/1403125000000000000000000000000 : ℝ)*base71 + (1821362820873/1122500000000000000000000000 : ℝ)*base74 + (6071441583578747/350781250000000000000000000000 : ℝ)*base75 + (4279911824670631/701562500000000000000000000000 : ℝ)*base78 + (22370178772769387/1403125000000000000000000000000 : ℝ)*base80 + (1989575007537/1122500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (32530069/10000000000000000000000 : ℝ)*base89 + (32530069/10000000000000000000000 : ℝ)*base91 + (32530069/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1372_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1372_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1372_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1599/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1372_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1372_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1372_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1599/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
