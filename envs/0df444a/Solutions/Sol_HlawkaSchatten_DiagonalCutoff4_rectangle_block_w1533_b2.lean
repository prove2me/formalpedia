-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1533_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:34.654041+00:00
-- url     : https://prove2.me/submissions/4f77ef9e-d177-4cb1-9b9f-04e1e46e57fe

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
theorem support_rectangle_w1533_s6_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-918716851/5000000000 : ℝ)*x 0 + (1357628683/2500000000 : ℝ)*x 1 + (326164301/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918716851/5000000000 : ℝ)^4563 ≤ (11254166426499/100000000000000 : ℝ)^3539 := by
    have hnat : (918716851 : ℕ)^4563*100000000000000^3539 ≤ 11254166426499^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918716851 5000000000 11254166426499 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357628683/2500000000 : ℝ)^4563 ≤ (568889573897/1250000000000 : ℝ)^3539 := by
    have hnat : (1357628683 : ℕ)^4563*1250000000000^3539 ≤ 568889573897^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357628683 2500000000 568889573897 1250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326164301/625000000 : ℝ)^4563 ≤ (21617333823459/50000000000000 : ℝ)^3539 := by
    have hnat : (326164301 : ℕ)^4563*50000000000000^3539 ≤ 21617333823459^3539*625000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326164301 625000000 21617333823459 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-918716851/5000000000 : ℝ), (1357628683/2500000000 : ℝ), (326164301/625000000 : ℝ)] ![(11254166426499/100000000000000 : ℝ), (568889573897/1250000000000 : ℝ), (21617333823459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-918716851/5000000000 : ℝ)|^4563 ≤ (11254166426499/100000000000000 : ℝ)^3539
        have hw : |(-918716851/5000000000 : ℝ)|=(918716851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357628683/2500000000 : ℝ)|^4563 ≤ (568889573897/1250000000000 : ℝ)^3539
        have hw : |(1357628683/2500000000 : ℝ)|=(1357628683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326164301/625000000 : ℝ)|^4563 ≤ (21617333823459/50000000000000 : ℝ)^3539
        have hw : |(326164301/625000000 : ℝ)|=(326164301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s6_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675199397/5000000000 : ℝ)*x 0 + (-97295313/500000000 : ℝ)*x 1 + (5218628791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675199397/5000000000 : ℝ)^4563 ≤ (44647323354957/100000000000000 : ℝ)^3539 := by
    have hnat : (2675199397 : ℕ)^4563*100000000000000^3539 ≤ 44647323354957^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675199397 5000000000 44647323354957 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97295313/500000000 : ℝ)^4563 ≤ (3029502313107/25000000000000 : ℝ)^3539 := by
    have hnat : (97295313 : ℕ)^4563*25000000000000^3539 ≤ 3029502313107^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97295313 500000000 3029502313107 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218628791/10000000000 : ℝ)^4563 ≤ (1351083355621/3125000000000 : ℝ)^3539 := by
    have hnat : (5218628791 : ℕ)^4563*3125000000000^3539 ≤ 1351083355621^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218628791 10000000000 1351083355621 3125000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675199397/5000000000 : ℝ), (-97295313/500000000 : ℝ), (5218628791/10000000000 : ℝ)] ![(44647323354957/100000000000000 : ℝ), (3029502313107/25000000000000 : ℝ), (1351083355621/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675199397/5000000000 : ℝ)|^4563 ≤ (44647323354957/100000000000000 : ℝ)^3539
        have hw : |(2675199397/5000000000 : ℝ)|=(2675199397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97295313/500000000 : ℝ)|^4563 ≤ (3029502313107/25000000000000 : ℝ)^3539
        have hw : |(-97295313/500000000 : ℝ)|=(97295313/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218628791/10000000000 : ℝ)|^4563 ≤ (1351083355621/3125000000000 : ℝ)^3539
        have hw : |(5218628791/10000000000 : ℝ)|=(5218628791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s6_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350398821/10000000000 : ℝ)*x 0 + (2609314373/5000000000 : ℝ)*x 1 + (-486476571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350398821/10000000000 : ℝ)^4563 ≤ (8929464729091/20000000000000 : ℝ)^3539 := by
    have hnat : (5350398821 : ℕ)^4563*20000000000000^3539 ≤ 8929464729091^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350398821 10000000000 8929464729091 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609314373/5000000000 : ℝ)^4563 ≤ (4323466689919/10000000000000 : ℝ)^3539 := by
    have hnat : (2609314373 : ℕ)^4563*10000000000000^3539 ≤ 4323466689919^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609314373 5000000000 4323466689919 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486476571/2500000000 : ℝ)^4563 ≤ (3029502361283/25000000000000 : ℝ)^3539 := by
    have hnat : (486476571 : ℕ)^4563*25000000000000^3539 ≤ 3029502361283^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486476571 2500000000 3029502361283 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350398821/10000000000 : ℝ), (2609314373/5000000000 : ℝ), (-486476571/2500000000 : ℝ)] ![(8929464729091/20000000000000 : ℝ), (4323466689919/10000000000000 : ℝ), (3029502361283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350398821/10000000000 : ℝ)|^4563 ≤ (8929464729091/20000000000000 : ℝ)^3539
        have hw : |(5350398821/10000000000 : ℝ)|=(5350398821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609314373/5000000000 : ℝ)|^4563 ≤ (4323466689919/10000000000000 : ℝ)^3539
        have hw : |(2609314373/5000000000 : ℝ)|=(2609314373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-486476571/2500000000 : ℝ)|^4563 ≤ (3029502361283/25000000000000 : ℝ)^3539
        have hw : |(-486476571/2500000000 : ℝ)|=(486476571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s6_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106502293/250000000 : ℝ)*x 0 + (4022118933/10000000000 : ℝ)*x 1 + (4509706751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106502293/250000000 : ℝ)^4563 ≤ (8320172716611/25000000000000 : ℝ)^3539 := by
    have hnat : (106502293 : ℕ)^4563*25000000000000^3539 ≤ 8320172716611^3539*250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106502293 250000000 8320172716611 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022118933/10000000000 : ℝ)^4563 ≤ (15451655579479/50000000000000 : ℝ)^3539 := by
    have hnat : (4022118933 : ℕ)^4563*50000000000000^3539 ≤ 15451655579479^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022118933 10000000000 15451655579479 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509706751/10000000000 : ℝ)^4563 ≤ (35815997957259/100000000000000 : ℝ)^3539 := by
    have hnat : (4509706751 : ℕ)^4563*100000000000000^3539 ≤ 35815997957259^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509706751 10000000000 35815997957259 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106502293/250000000 : ℝ), (4022118933/10000000000 : ℝ), (4509706751/10000000000 : ℝ)] ![(8320172716611/25000000000000 : ℝ), (15451655579479/50000000000000 : ℝ), (35815997957259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106502293/250000000 : ℝ)|^4563 ≤ (8320172716611/25000000000000 : ℝ)^3539
        have hw : |(106502293/250000000 : ℝ)|=(106502293/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022118933/10000000000 : ℝ)|^4563 ≤ (15451655579479/50000000000000 : ℝ)^3539
        have hw : |(4022118933/10000000000 : ℝ)|=(4022118933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509706751/10000000000 : ℝ)|^4563 ≤ (35815997957259/100000000000000 : ℝ)^3539
        have hw : |(4509706751/10000000000 : ℝ)|=(4509706751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s6_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-367492389/2000000000 : ℝ)*x 0 + (260986201/500000000 : ℝ)*x 1 + (5429411361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367492389/2000000000 : ℝ)^4563 ≤ (2250877893361/20000000000000 : ℝ)^3539 := by
    have hnat : (367492389 : ℕ)^4563*20000000000000^3539 ≤ 2250877893361^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367492389 2000000000 2250877893361 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260986201/500000000 : ℝ)^4563 ≤ (4324636678399/10000000000000 : ℝ)^3539 := by
    have hnat : (260986201 : ℕ)^4563*10000000000000^3539 ≤ 4324636678399^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260986201 500000000 4324636678399 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429411361/10000000000 : ℝ)^4563 ≤ (2843702733243/6250000000000 : ℝ)^3539 := by
    have hnat : (5429411361 : ℕ)^4563*6250000000000^3539 ≤ 2843702733243^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429411361 10000000000 2843702733243 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367492389/2000000000 : ℝ), (260986201/500000000 : ℝ), (5429411361/10000000000 : ℝ)] ![(2250877893361/20000000000000 : ℝ), (4324636678399/10000000000000 : ℝ), (2843702733243/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367492389/2000000000 : ℝ)|^4563 ≤ (2250877893361/20000000000000 : ℝ)^3539
        have hw : |(-367492389/2000000000 : ℝ)|=(367492389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260986201/500000000 : ℝ)|^4563 ≤ (4324636678399/10000000000000 : ℝ)^3539
        have hw : |(260986201/500000000 : ℝ)|=(260986201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429411361/10000000000 : ℝ)|^4563 ≤ (2843702733243/6250000000000 : ℝ)^3539
        have hw : |(5429411361/10000000000 : ℝ)|=(5429411361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s6_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647303263/5000000000 : ℝ)*x 0 + (-1735123679/10000000000 : ℝ)*x 1 + (5429411449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647303263/5000000000 : ℝ)^4563 ≤ (8809590425161/20000000000000 : ℝ)^3539 := by
    have hnat : (2647303263 : ℕ)^4563*20000000000000^3539 ≤ 8809590425161^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647303263 5000000000 8809590425161 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735123679/10000000000 : ℝ)^4563 ≤ (5226401585269/50000000000000 : ℝ)^3539 := by
    have hnat : (1735123679 : ℕ)^4563*50000000000000^3539 ≤ 5226401585269^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735123679 10000000000 5226401585269 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429411449/10000000000 : ℝ)^4563 ≤ (45499244682721/100000000000000 : ℝ)^3539 := by
    have hnat : (5429411449 : ℕ)^4563*100000000000000^3539 ≤ 45499244682721^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429411449 10000000000 45499244682721 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647303263/5000000000 : ℝ), (-1735123679/10000000000 : ℝ), (5429411449/10000000000 : ℝ)] ![(8809590425161/20000000000000 : ℝ), (5226401585269/50000000000000 : ℝ), (45499244682721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647303263/5000000000 : ℝ)|^4563 ≤ (8809590425161/20000000000000 : ℝ)^3539
        have hw : |(2647303263/5000000000 : ℝ)|=(2647303263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1735123679/10000000000 : ℝ)|^4563 ≤ (5226401585269/50000000000000 : ℝ)^3539
        have hw : |(-1735123679/10000000000 : ℝ)|=(1735123679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429411449/10000000000 : ℝ)|^4563 ≤ (45499244682721/100000000000000 : ℝ)^3539
        have hw : |(5429411449/10000000000 : ℝ)|=(5429411449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s6_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294606651/10000000000 : ℝ)*x 0 + (1357352853/2500000000 : ℝ)*x 1 + (-1735123559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294606651/10000000000 : ℝ)^4563 ≤ (4404795346663/10000000000000 : ℝ)^3539 := by
    have hnat : (5294606651 : ℕ)^4563*10000000000000^3539 ≤ 4404795346663^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294606651 10000000000 4404795346663 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357352853/2500000000 : ℝ)^4563 ≤ (45499244282939/100000000000000 : ℝ)^3539 := by
    have hnat : (1357352853 : ℕ)^4563*100000000000000^3539 ≤ 45499244282939^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357352853 2500000000 45499244282939 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1735123559/10000000000 : ℝ)^4563 ≤ (5226401119229/50000000000000 : ℝ)^3539 := by
    have hnat : (1735123559 : ℕ)^4563*50000000000000^3539 ≤ 5226401119229^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735123559 10000000000 5226401119229 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294606651/10000000000 : ℝ), (1357352853/2500000000 : ℝ), (-1735123559/10000000000 : ℝ)] ![(4404795346663/10000000000000 : ℝ), (45499244282939/100000000000000 : ℝ), (5226401119229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294606651/10000000000 : ℝ)|^4563 ≤ (4404795346663/10000000000000 : ℝ)^3539
        have hw : |(5294606651/10000000000 : ℝ)|=(5294606651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357352853/2500000000 : ℝ)|^4563 ≤ (45499244282939/100000000000000 : ℝ)^3539
        have hw : |(1357352853/2500000000 : ℝ)|=(1357352853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1735123559/10000000000 : ℝ)|^4563 ≤ (5226401119229/50000000000000 : ℝ)^3539
        have hw : |(-1735123559/10000000000 : ℝ)|=(1735123559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s6_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260156943/10000000000 : ℝ)*x 0 + (180287443/400000000 : ℝ)*x 1 + (4024657701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260156943/10000000000 : ℝ)^4563 ≤ (33281347835663/100000000000000 : ℝ)^3539 := by
    have hnat : (4260156943 : ℕ)^4563*100000000000000^3539 ≤ 33281347835663^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260156943 10000000000 33281347835663 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180287443/400000000 : ℝ)^4563 ≤ (35790188399579/100000000000000 : ℝ)^3539 := by
    have hnat : (180287443 : ℕ)^4563*100000000000000^3539 ≤ 35790188399579^3539*400000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180287443 400000000 35790188399579 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024657701/10000000000 : ℝ)^4563 ≤ (6185692749417/20000000000000 : ℝ)^3539 := by
    have hnat : (4024657701 : ℕ)^4563*20000000000000^3539 ≤ 6185692749417^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024657701 10000000000 6185692749417 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260156943/10000000000 : ℝ), (180287443/400000000 : ℝ), (4024657701/10000000000 : ℝ)] ![(33281347835663/100000000000000 : ℝ), (35790188399579/100000000000000 : ℝ), (6185692749417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260156943/10000000000 : ℝ)|^4563 ≤ (33281347835663/100000000000000 : ℝ)^3539
        have hw : |(4260156943/10000000000 : ℝ)|=(4260156943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180287443/400000000 : ℝ)|^4563 ≤ (35790188399579/100000000000000 : ℝ)^3539
        have hw : |(180287443/400000000 : ℝ)|=(180287443/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024657701/10000000000 : ℝ)|^4563 ≤ (6185692749417/20000000000000 : ℝ)^3539
        have hw : |(4024657701/10000000000 : ℝ)|=(4024657701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2199/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5497/50000 : ℝ) ^ (4561/1024 : ℝ) ≤ (134014027506343/2500000000000000000 : ℝ) := by
    have hpowers : (5497/50000 : ℝ)^4561 ≤ (134014027506343/2500000000000000000 : ℝ)^1024 := by
      have hnat : (5497 : ℕ)^4561*2500000000000000000^1024 ≤ 134014027506343^1024*50000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5497 50000 134014027506343 2500000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5497/50000 : ℝ)) (X := (134014027506343/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4561/1024 : ℝ) ≤ (24648032237500861/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4561 ≤ (24648032237500861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4561*100000000000000000000^1024 ≤ 24648032237500861^1024*20000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 24648032237500861 100000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (24648032237500861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250134014027506343/1250000000000000000 : ℝ) ≤ (5000120346116899/5000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (1250134014027506343/1250000000000000000 : ℝ)^1024 ≤ (5000120346116899/5000000000000000 : ℝ)^4561 := by
      have hnat : (1250134014027506343 : ℕ)^1024*5000000000000000^4561 ≤ 5000120346116899^4561*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250134014027506343 1250000000000000000 5000120346116899 5000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000120346116899/5000000000000000 : ℝ)) (X := (1250134014027506343/1250000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030008593337754581/100000000000000000000 : ℝ) ≤ (5000336825528583/5000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (100030008593337754581/100000000000000000000 : ℝ)^1024 ≤ (5000336825528583/5000000000000000 : ℝ)^4561 := by
      have hnat : (100030008593337754581 : ℕ)^1024*5000000000000000^4561 ≤ 5000336825528583^4561*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030008593337754581 100000000000000000000 5000336825528583 5000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000336825528583/5000000000000000 : ℝ)) (X := (100030008593337754581/100000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024648032237500861/50000000000000000000 : ℝ) ≤ (5000553304940267/5000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50024648032237500861/50000000000000000000 : ℝ)^1024 ≤ (5000553304940267/5000000000000000 : ℝ)^4561 := by
      have hnat : (50024648032237500861 : ℕ)^1024*5000000000000000^4561 ≤ 5000553304940267^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024648032237500861 50000000000000000000 5000553304940267 5000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000553304940267/5000000000000000 : ℝ)) (X := (50024648032237500861/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(134014027506343/2500000000000000000 : ℝ) ≤ ((22450780525106885617/22455000000000000000 : ℝ)+2*(54119852921/56137500000000 : ℝ)*(5497/50000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (22450780525106885617/22455000000000000000 : ℝ)+2*(54119852921/56137500000000 : ℝ)*(5497/50000 : ℝ)=(5000120346116899/5000000000000000 : ℝ) by norm_num, show 1+2*(134014027506343/2500000000000000000 : ℝ)=(1250134014027506343/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24648032237500861/100000000000000000000 : ℝ)+(134014027506343/2500000000000000000 : ℝ) ≤ ((22450780525106885617/22455000000000000000 : ℝ)+(54119852921/56137500000000 : ℝ)*((3097/20000 : ℝ)+(5497/50000 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (22450780525106885617/22455000000000000000 : ℝ)+(54119852921/56137500000000 : ℝ)*((3097/20000 : ℝ)+(5497/50000 : ℝ))=(5000336825528583/5000000000000000 : ℝ) by norm_num, show 1+(24648032237500861/100000000000000000000 : ℝ)+(134014027506343/2500000000000000000 : ℝ)=(100030008593337754581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24648032237500861/100000000000000000000 : ℝ) ≤ ((22450780525106885617/22455000000000000000 : ℝ)+2*(54119852921/56137500000000 : ℝ)*(3097/20000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (22450780525106885617/22455000000000000000 : ℝ)+2*(54119852921/56137500000000 : ℝ)*(3097/20000 : ℝ)=(5000553304940267/5000000000000000 : ℝ) by norm_num, show 1+2*(24648032237500861/100000000000000000000 : ℝ)=(50024648032237500861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22450780525106885617/22455000000000000000 : ℝ)*(X 1 0+X 2 0)+(54119852921/56137500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22450780525106885617/22455000000000000000 : ℝ)) (alpha := (54119852921/56137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22450780525106885617/22455000000000000000 : ℝ)*(X 0 1+X 2 1)+(54119852921/56137500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22450780525106885617/22455000000000000000 : ℝ)) (alpha := (54119852921/56137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22450780525106885617/22455000000000000000 : ℝ)*(X 0 2+X 1 2)+(54119852921/56137500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22450780525106885617/22455000000000000000 : ℝ)) (alpha := (54119852921/56137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-918716851/5000000000 : ℝ)*X 0 0+(1357628683/2500000000 : ℝ)*X 0 1+(326164301/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675199397/5000000000 : ℝ)*X 1 0+(-97295313/500000000 : ℝ)*X 1 1+(5218628791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350398821/10000000000 : ℝ)*X 2 0+(2609314373/5000000000 : ℝ)*X 2 1+(-486476571/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((106502293/250000000 : ℝ)*X 0 0+(4022118933/10000000000 : ℝ)*X 0 1+(4509706751/10000000000 : ℝ)*X 0 2+(106502293/250000000 : ℝ)*X 1 0+(4022118933/10000000000 : ℝ)*X 1 1+(4509706751/10000000000 : ℝ)*X 1 2+(106502293/250000000 : ℝ)*X 2 0+(4022118933/10000000000 : ℝ)*X 2 1+(4509706751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-367492389/2000000000 : ℝ)*X 0 0+(260986201/500000000 : ℝ)*X 0 1+(5429411361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647303263/5000000000 : ℝ)*X 1 0+(-1735123679/10000000000 : ℝ)*X 1 1+(5429411449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294606651/10000000000 : ℝ)*X 2 0+(1357352853/2500000000 : ℝ)*X 2 1+(-1735123559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260156943/10000000000 : ℝ)*X 0 0+(180287443/400000000 : ℝ)*X 0 1+(4024657701/10000000000 : ℝ)*X 0 2+(4260156943/10000000000 : ℝ)*X 1 0+(180287443/400000000 : ℝ)*X 1 1+(4024657701/10000000000 : ℝ)*X 1 2+(4260156943/10000000000 : ℝ)*X 2 0+(180287443/400000000 : ℝ)*X 2 1+(4024657701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5634590901534730946743/2495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (455999461/100000000000000 : ℝ)*(base19) + (238407749/50000000000000 : ℝ)*(base23) + (1605333/100000000000000 : ℝ)*(lower2) + (121229/195312500000 : ℝ)*(upper3) + (2519749/6250000000000 : ℝ)*(upper5) + (1692613550943471/50000000000000 : ℝ)*(major0) + (1692613550943471/50000000000000 : ℝ)*(major1) + (1692613550943471/50000000000000 : ℝ)*(major2) + (943905624019027/20000000000000 : ℝ)*(sp0) + (2359767251737629/50000000000000 : ℝ)*(sp1) + (235976724132961/5000000000000 : ℝ)*(sp2) + (2050915718622637/100000000000000 : ℝ)*(sp3) + (53432653/781250000000 : ℝ)*(sp4) + (3450398087/100000000000000 : ℝ)*(sp7) + (512729792255181/25000000000000 : ℝ)*(f.failure) + (4719534959474719/100000000000000 : ℝ)*(f.sum) + (14764272766517/7485000000000000000000000000 : ℝ)*base65 + (91809642319460377/124750000000000000000000000000000 : ℝ)*base68 + (658579208066460377/124750000000000000000000000000000 : ℝ)*base70 + (342256587102289623/124750000000000000000000000000000 : ℝ)*base71 + (11252829227521/3742500000000000000000000000 : ℝ)*base73 + (1309959972542960377/124750000000000000000000000000000 : ℝ)*base76 + (788769176294289623/124750000000000000000000000000000 : ℝ)*base77 + (949540780585539623/124750000000000000000000000000000 : ℝ)*base79 + (11337619811519/3742500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8037801/2500000000000000000000 : ℝ)*base89 + (8037801/2500000000000000000000 : ℝ)*base91 + (8037801/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2080979118522015481102079431/374250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236704733/20000000000000 : ℝ)*(base19) + (370098693/25000000000000 : ℝ)*(base23) + (96244017/25000000000000 : ℝ)*(lower1) + (197930991/100000000000000 : ℝ)*(upper3) + (69522021/100000000000000 : ℝ)*(lower4) + (206465511/100000000000000 : ℝ)*(upper5) + (3420697827351257/100000000000000 : ℝ)*(major0) + (3420697827351257/100000000000000 : ℝ)*(major1) + (3420697827351257/100000000000000 : ℝ)*(major2) + (1256772687/25000000000000 : ℝ)*(sp2) + (59612332223771/1250000000000 : ℝ)*(sp4) + (953797078875603/20000000000000 : ℝ)*(sp5) + (29806125440101/625000000000 : ℝ)*(sp6) + (2072408891454201/100000000000000 : ℝ)*(sp7) + (2072408891454201/100000000000000 : ℝ)*(f.failure) + (59612332223771/1250000000000 : ℝ)*(f.sum) + (43849763446489/22455000000000000000000000000 : ℝ)*base66 + (8161958715050392159/249500000000000000000000000000000 : ℝ)*base68 + (1767633875302607841/249500000000000000000000000000000 : ℝ)*base69 + (12370397160171392159/249500000000000000000000000000000 : ℝ)*base72 + (34711139863187/11227500000000000000000000000 : ℝ)*base74 + (16253128015180107841/249500000000000000000000000000000 : ℝ)*base75 + (527963826517607841/249500000000000000000000000000000 : ℝ)*base77 + (2151795856113607841/249500000000000000000000000000000 : ℝ)*base79 + (59070975632381/22455000000000000000000000000 : ℝ)*base81 + (16602779/10000000000000000000000 : ℝ)*base90 + (16602779/10000000000000000000000 : ℝ)*base92 + (16602779/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1533_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1533_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1533_box_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65099603/400000000 : ℝ)*x 0 + (675070691/1250000000 : ℝ)*x 1 + (270028247/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65099603/400000000 : ℝ)^4563 ≤ (9624392654777/100000000000000 : ℝ)^3539 := by
    have hnat : (65099603 : ℕ)^4563*100000000000000^3539 ≤ 9624392654777^3539*400000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65099603 400000000 9624392654777 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675070691/1250000000 : ℝ)^4563 ≤ (45187806838677/100000000000000 : ℝ)^3539 := by
    have hnat : (675070691 : ℕ)^4563*100000000000000^3539 ≤ 45187806838677^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675070691 1250000000 45187806838677 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270028247/500000000 : ℝ)^4563 ≤ (11296950123793/25000000000000 : ℝ)^3539 := by
    have hnat : (270028247 : ℕ)^4563*25000000000000^3539 ≤ 11296950123793^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270028247 500000000 11296950123793 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65099603/400000000 : ℝ), (675070691/1250000000 : ℝ), (270028247/500000000 : ℝ)] ![(9624392654777/100000000000000 : ℝ), (45187806838677/100000000000000 : ℝ), (11296950123793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65099603/400000000 : ℝ)|^4563 ≤ (9624392654777/100000000000000 : ℝ)^3539
        have hw : |(-65099603/400000000 : ℝ)|=(65099603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675070691/1250000000 : ℝ)|^4563 ≤ (45187806838677/100000000000000 : ℝ)^3539
        have hw : |(675070691/1250000000 : ℝ)|=(675070691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270028247/500000000 : ℝ)|^4563 ≤ (11296950123793/25000000000000 : ℝ)^3539
        have hw : |(270028247/500000000 : ℝ)|=(270028247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317749017/2500000000 : ℝ)*x 0 + (-361474499/2000000000 : ℝ)*x 1 + (5400566019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317749017/2500000000 : ℝ)^4563 ≤ (2189742791841/5000000000000 : ℝ)^3539 := by
    have hnat : (1317749017 : ℕ)^4563*5000000000000^3539 ≤ 2189742791841^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317749017 2500000000 2189742791841 5000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361474499/2000000000 : ℝ)^4563 ≤ (1101733202077/10000000000000 : ℝ)^3539 := by
    have hnat : (361474499 : ℕ)^4563*10000000000000^3539 ≤ 1101733202077^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361474499 2000000000 1101733202077 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400566019/10000000000 : ℝ)^4563 ≤ (45187812135719/100000000000000 : ℝ)^3539 := by
    have hnat : (5400566019 : ℕ)^4563*100000000000000^3539 ≤ 45187812135719^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400566019 10000000000 45187812135719 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317749017/2500000000 : ℝ), (-361474499/2000000000 : ℝ), (5400566019/10000000000 : ℝ)] ![(2189742791841/5000000000000 : ℝ), (1101733202077/10000000000000 : ℝ), (45187812135719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317749017/2500000000 : ℝ)|^4563 ≤ (2189742791841/5000000000000 : ℝ)^3539
        have hw : |(1317749017/2500000000 : ℝ)|=(1317749017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-361474499/2000000000 : ℝ)|^4563 ≤ (1101733202077/10000000000000 : ℝ)^3539
        have hw : |(-361474499/2000000000 : ℝ)|=(361474499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400566019/10000000000 : ℝ)|^4563 ≤ (45187812135719/100000000000000 : ℝ)^3539
        have hw : |(5400566019/10000000000 : ℝ)|=(5400566019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270996479/10000000000 : ℝ)*x 0 + (5400565579/10000000000 : ℝ)*x 1 + (-903686269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270996479/10000000000 : ℝ)^4563 ≤ (43794860239753/100000000000000 : ℝ)^3539 := by
    have hnat : (5270996479 : ℕ)^4563*100000000000000^3539 ≤ 43794860239753^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270996479 10000000000 43794860239753 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400565579/10000000000 : ℝ)^4563 ≤ (22593903694439/50000000000000 : ℝ)^3539 := by
    have hnat : (5400565579 : ℕ)^4563*50000000000000^3539 ≤ 22593903694439^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400565579 10000000000 22593903694439 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903686269/5000000000 : ℝ)^4563 ≤ (11017332358731/100000000000000 : ℝ)^3539 := by
    have hnat : (903686269 : ℕ)^4563*100000000000000^3539 ≤ 11017332358731^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903686269 5000000000 11017332358731 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270996479/10000000000 : ℝ), (5400565579/10000000000 : ℝ), (-903686269/5000000000 : ℝ)] ![(43794860239753/100000000000000 : ℝ), (22593903694439/50000000000000 : ℝ), (11017332358731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270996479/10000000000 : ℝ)|^4563 ≤ (43794860239753/100000000000000 : ℝ)^3539
        have hw : |(5270996479/10000000000 : ℝ)|=(5270996479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400565579/10000000000 : ℝ)|^4563 ≤ (22593903694439/50000000000000 : ℝ)^3539
        have hw : |(5400565579/10000000000 : ℝ)|=(5400565579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903686269/5000000000 : ℝ)|^4563 ≤ (11017332358731/100000000000000 : ℝ)^3539
        have hw : |(-903686269/5000000000 : ℝ)|=(903686269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2231117613/5000000000 : ℝ)*x 0 + (208293499/500000000 : ℝ)*x 1 + (2082935121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2231117613/5000000000 : ℝ)^4563 ≤ (706612662873/2000000000000 : ℝ)^3539 := by
    have hnat : (2231117613 : ℕ)^4563*2000000000000^3539 ≤ 706612662873^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231117613 5000000000 706612662873 2000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208293499/500000000 : ℝ)^4563 ≤ (32334682110203/100000000000000 : ℝ)^3539 := by
    have hnat : (208293499 : ℕ)^4563*100000000000000^3539 ≤ 32334682110203^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208293499 500000000 32334682110203 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082935121/5000000000 : ℝ)^4563 ≤ (32334684732211/100000000000000 : ℝ)^3539 := by
    have hnat : (2082935121 : ℕ)^4563*100000000000000^3539 ≤ 32334684732211^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082935121 5000000000 32334684732211 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2231117613/5000000000 : ℝ), (208293499/500000000 : ℝ), (2082935121/5000000000 : ℝ)] ![(706612662873/2000000000000 : ℝ), (32334682110203/100000000000000 : ℝ), (32334684732211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2231117613/5000000000 : ℝ)|^4563 ≤ (706612662873/2000000000000 : ℝ)^3539
        have hw : |(2231117613/5000000000 : ℝ)|=(2231117613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208293499/500000000 : ℝ)|^4563 ≤ (32334682110203/100000000000000 : ℝ)^3539
        have hw : |(208293499/500000000 : ℝ)|=(208293499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2082935121/5000000000 : ℝ)|^4563 ≤ (32334684732211/100000000000000 : ℝ)^3539
        have hw : |(2082935121/5000000000 : ℝ)|=(2082935121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026399921/5000000000 : ℝ)*x 0 + (2622122047/5000000000 : ℝ)*x 1 + (2622122663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026399921/5000000000 : ℝ)^4563 ≤ (51932109283/400000000000 : ℝ)^3539 := by
    have hnat : (1026399921 : ℕ)^4563*400000000000^3539 ≤ 51932109283^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026399921 5000000000 51932109283 400000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622122047/5000000000 : ℝ)^4563 ≤ (43508479743671/100000000000000 : ℝ)^3539 := by
    have hnat : (2622122047 : ℕ)^4563*100000000000000^3539 ≤ 43508479743671^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622122047 5000000000 43508479743671 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622122663/5000000000 : ℝ)^4563 ≤ (43508492922343/100000000000000 : ℝ)^3539 := by
    have hnat : (2622122663 : ℕ)^4563*100000000000000^3539 ≤ 43508492922343^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622122663 5000000000 43508492922343 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026399921/5000000000 : ℝ), (2622122047/5000000000 : ℝ), (2622122663/5000000000 : ℝ)] ![(51932109283/400000000000 : ℝ), (43508479743671/100000000000000 : ℝ), (43508492922343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026399921/5000000000 : ℝ)|^4563 ≤ (51932109283/400000000000 : ℝ)^3539
        have hw : |(-1026399921/5000000000 : ℝ)|=(1026399921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622122047/5000000000 : ℝ)|^4563 ≤ (43508479743671/100000000000000 : ℝ)^3539
        have hw : |(2622122047/5000000000 : ℝ)|=(2622122047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622122663/5000000000 : ℝ)|^4563 ≤ (43508492922343/100000000000000 : ℝ)^3539
        have hw : |(2622122663/5000000000 : ℝ)|=(2622122663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379656329/10000000000 : ℝ)*x 0 + (-1872160333/10000000000 : ℝ)*x 1 + (5244244653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379656329/10000000000 : ℝ)^4563 ≤ (5620294894649/12500000000000 : ℝ)^3539 := by
    have hnat : (5379656329 : ℕ)^4563*12500000000000^3539 ≤ 5620294894649^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379656329 10000000000 5620294894649 12500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872160333/10000000000 : ℝ)^4563 ≤ (11529155102129/100000000000000 : ℝ)^3539 := by
    have hnat : (1872160333 : ℕ)^4563*100000000000000^3539 ≤ 11529155102129^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872160333 10000000000 11529155102129 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244244653/10000000000 : ℝ)^4563 ≤ (543856071541/1250000000000 : ℝ)^3539 := by
    have hnat : (5244244653 : ℕ)^4563*1250000000000^3539 ≤ 543856071541^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244244653 10000000000 543856071541 1250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379656329/10000000000 : ℝ), (-1872160333/10000000000 : ℝ), (5244244653/10000000000 : ℝ)] ![(5620294894649/12500000000000 : ℝ), (11529155102129/100000000000000 : ℝ), (543856071541/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379656329/10000000000 : ℝ)|^4563 ≤ (5620294894649/12500000000000 : ℝ)^3539
        have hw : |(5379656329/10000000000 : ℝ)|=(5379656329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1872160333/10000000000 : ℝ)|^4563 ≤ (11529155102129/100000000000000 : ℝ)^3539
        have hw : |(-1872160333/10000000000 : ℝ)|=(1872160333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244244653/10000000000 : ℝ)|^4563 ≤ (543856071541/1250000000000 : ℝ)^3539
        have hw : |(5244244653/10000000000 : ℝ)|=(5244244653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344913937/2500000000 : ℝ)*x 0 + (5244244479/10000000000 : ℝ)*x 1 + (-468040339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344913937/2500000000 : ℝ)^4563 ≤ (44962352896237/100000000000000 : ℝ)^3539 := by
    have hnat : (1344913937 : ℕ)^4563*100000000000000^3539 ≤ 44962352896237^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344913937 2500000000 44962352896237 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244244479/10000000000 : ℝ)^4563 ≤ (21754241931003/50000000000000 : ℝ)^3539 := by
    have hnat : (5244244479 : ℕ)^4563*50000000000000^3539 ≤ 21754241931003^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244244479 10000000000 21754241931003 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468040339/2500000000 : ℝ)^4563 ≤ (11529163224821/100000000000000 : ℝ)^3539 := by
    have hnat : (468040339 : ℕ)^4563*100000000000000^3539 ≤ 11529163224821^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468040339 2500000000 11529163224821 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344913937/2500000000 : ℝ), (5244244479/10000000000 : ℝ), (-468040339/2500000000 : ℝ)] ![(44962352896237/100000000000000 : ℝ), (21754241931003/50000000000000 : ℝ), (11529163224821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344913937/2500000000 : ℝ)|^4563 ≤ (44962352896237/100000000000000 : ℝ)^3539
        have hw : |(1344913937/2500000000 : ℝ)|=(1344913937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244244479/10000000000 : ℝ)|^4563 ≤ (21754241931003/50000000000000 : ℝ)^3539
        have hw : |(5244244479/10000000000 : ℝ)|=(5244244479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468040339/2500000000 : ℝ)|^4563 ≤ (11529163224821/100000000000000 : ℝ)^3539
        have hw : |(-468040339/2500000000 : ℝ)|=(468040339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (811085809/2000000000 : ℝ)*x 0 + (174765683/400000000 : ℝ)*x 1 + (2184570509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811085809/2000000000 : ℝ)^4563 ≤ (31233692207439/100000000000000 : ℝ)^3539 := by
    have hnat : (811085809 : ℕ)^4563*100000000000000^3539 ≤ 31233692207439^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811085809 2000000000 31233692207439 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174765683/400000000 : ℝ)^4563 ≤ (17191579627143/50000000000000 : ℝ)^3539 := by
    have hnat : (174765683 : ℕ)^4563*50000000000000^3539 ≤ 17191579627143^3539*400000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174765683 400000000 17191579627143 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184570509/5000000000 : ℝ)^4563 ≤ (6876629705871/20000000000000 : ℝ)^3539 := by
    have hnat : (2184570509 : ℕ)^4563*20000000000000^3539 ≤ 6876629705871^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184570509 5000000000 6876629705871 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(811085809/2000000000 : ℝ), (174765683/400000000 : ℝ), (2184570509/5000000000 : ℝ)] ![(31233692207439/100000000000000 : ℝ), (17191579627143/50000000000000 : ℝ), (6876629705871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(811085809/2000000000 : ℝ)|^4563 ≤ (31233692207439/100000000000000 : ℝ)^3539
        have hw : |(811085809/2000000000 : ℝ)|=(811085809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(174765683/400000000 : ℝ)|^4563 ≤ (17191579627143/50000000000000 : ℝ)^3539
        have hw : |(174765683/400000000 : ℝ)|=(174765683/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2184570509/5000000000 : ℝ)|^4563 ≤ (6876629705871/20000000000000 : ℝ)^3539
        have hw : |(2184570509/5000000000 : ℝ)|=(2184570509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_8 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-392563167/2000000000 : ℝ)*x 0 + (256725189/500000000 : ℝ)*x 1 + (338809639/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392563167/2000000000 : ℝ)^4563 ≤ (11966750137/97656250000 : ℝ)^3539 := by
    have hnat : (392563167 : ℕ)^4563*97656250000^3539 ≤ 11966750137^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392563167 2000000000 11966750137 97656250000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256725189/500000000 : ℝ)^4563 ≤ (2646135134547/6250000000000 : ℝ)^3539 := by
    have hnat : (256725189 : ℕ)^4563*6250000000000^3539 ≤ 2646135134547^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256725189 500000000 2646135134547 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338809639/625000000 : ℝ)^4563 ≤ (45407885689119/100000000000000 : ℝ)^3539 := by
    have hnat : (338809639 : ℕ)^4563*100000000000000^3539 ≤ 45407885689119^3539*625000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338809639 625000000 45407885689119 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-392563167/2000000000 : ℝ), (256725189/500000000 : ℝ), (338809639/625000000 : ℝ)] ![(11966750137/97656250000 : ℝ), (2646135134547/6250000000000 : ℝ), (45407885689119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-392563167/2000000000 : ℝ)|^4563 ≤ (11966750137/97656250000 : ℝ)^3539
        have hw : |(-392563167/2000000000 : ℝ)|=(392563167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256725189/500000000 : ℝ)|^4563 ≤ (2646135134547/6250000000000 : ℝ)^3539
        have hw : |(256725189/500000000 : ℝ)|=(256725189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338809639/625000000 : ℝ)|^4563 ≤ (45407885689119/100000000000000 : ℝ)^3539
        have hw : |(338809639/625000000 : ℝ)|=(338809639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_9 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314204869/2500000000 : ℝ)*x 0 + (-1798681339/10000000000 : ℝ)*x 1 + (677619261/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314204869/2500000000 : ℝ)^4563 ≤ (21821522455637/50000000000000 : ℝ)^3539 := by
    have hnat : (1314204869 : ℕ)^4563*50000000000000^3539 ≤ 21821522455637^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314204869 2500000000 21821522455637 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798681339/10000000000 : ℝ)^4563 ≤ (10949070865647/100000000000000 : ℝ)^3539 := by
    have hnat : (1798681339 : ℕ)^4563*100000000000000^3539 ≤ 10949070865647^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798681339 10000000000 10949070865647 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677619261/1250000000 : ℝ)^4563 ≤ (22703942110157/50000000000000 : ℝ)^3539 := by
    have hnat : (677619261 : ℕ)^4563*50000000000000^3539 ≤ 22703942110157^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677619261 1250000000 22703942110157 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314204869/2500000000 : ℝ), (-1798681339/10000000000 : ℝ), (677619261/1250000000 : ℝ)] ![(21821522455637/50000000000000 : ℝ), (10949070865647/100000000000000 : ℝ), (22703942110157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314204869/2500000000 : ℝ)|^4563 ≤ (21821522455637/50000000000000 : ℝ)^3539
        have hw : |(1314204869/2500000000 : ℝ)|=(1314204869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1798681339/10000000000 : ℝ)|^4563 ≤ (10949070865647/100000000000000 : ℝ)^3539
        have hw : |(-1798681339/10000000000 : ℝ)|=(1798681339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677619261/1250000000 : ℝ)|^4563 ≤ (22703942110157/50000000000000 : ℝ)^3539
        have hw : |(677619261/1250000000 : ℝ)|=(677619261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_10 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8410911/16000000 : ℝ)*x 0 + (1355238583/2500000000 : ℝ)*x 1 + (-1798681139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8410911/16000000 : ℝ)^4563 ≤ (4364304383013/10000000000000 : ℝ)^3539 := by
    have hnat : (8410911 : ℕ)^4563*10000000000000^3539 ≤ 4364304383013^3539*16000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8410911 16000000 4364304383013 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355238583/2500000000 : ℝ)^4563 ≤ (11351971713881/25000000000000 : ℝ)^3539 := by
    have hnat : (1355238583 : ℕ)^4563*25000000000000^3539 ≤ 11351971713881^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355238583 2500000000 11351971713881 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1798681139/10000000000 : ℝ)^4563 ≤ (2737267323981/25000000000000 : ℝ)^3539 := by
    have hnat : (1798681139 : ℕ)^4563*25000000000000^3539 ≤ 2737267323981^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798681139 10000000000 2737267323981 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8410911/16000000 : ℝ), (1355238583/2500000000 : ℝ), (-1798681139/10000000000 : ℝ)] ![(4364304383013/10000000000000 : ℝ), (11351971713881/25000000000000 : ℝ), (2737267323981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8410911/16000000 : ℝ)|^4563 ≤ (4364304383013/10000000000000 : ℝ)^3539
        have hw : |(8410911/16000000 : ℝ)|=(8410911/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355238583/2500000000 : ℝ)|^4563 ≤ (11351971713881/25000000000000 : ℝ)^3539
        have hw : |(1355238583/2500000000 : ℝ)|=(1355238583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1798681139/10000000000 : ℝ)|^4563 ≤ (2737267323981/25000000000000 : ℝ)^3539
        have hw : |(-1798681139/10000000000 : ℝ)|=(1798681139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_11 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (564268213/1250000000 : ℝ)*x 0 + (4139324497/10000000000 : ℝ)*x 1 + (2069662383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564268213/1250000000 : ℝ)^4563 ≤ (4482682396467/12500000000000 : ℝ)^3539 := by
    have hnat : (564268213 : ℕ)^4563*12500000000000^3539 ≤ 4482682396467^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564268213 1250000000 4482682396467 12500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139324497/10000000000 : ℝ)^4563 ≤ (32069269065589/100000000000000 : ℝ)^3539 := by
    have hnat : (4139324497 : ℕ)^4563*100000000000000^3539 ≤ 32069269065589^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139324497 10000000000 32069269065589 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069662383/5000000000 : ℝ)^4563 ≤ (32069271752677/100000000000000 : ℝ)^3539 := by
    have hnat : (2069662383 : ℕ)^4563*100000000000000^3539 ≤ 32069271752677^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069662383 5000000000 32069271752677 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564268213/1250000000 : ℝ), (4139324497/10000000000 : ℝ), (2069662383/5000000000 : ℝ)] ![(4482682396467/12500000000000 : ℝ), (32069269065589/100000000000000 : ℝ), (32069271752677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564268213/1250000000 : ℝ)|^4563 ≤ (4482682396467/12500000000000 : ℝ)^3539
        have hw : |(564268213/1250000000 : ℝ)|=(564268213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139324497/10000000000 : ℝ)|^4563 ≤ (32069269065589/100000000000000 : ℝ)^3539
        have hw : |(4139324497/10000000000 : ℝ)|=(4139324497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2069662383/5000000000 : ℝ)|^4563 ≤ (32069271752677/100000000000000 : ℝ)^3539
        have hw : |(2069662383/5000000000 : ℝ)|=(2069662383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_12 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-343462573/2000000000 : ℝ)*x 0 + (5506847867/10000000000 : ℝ)*x 1 + (1307301263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343462573/2000000000 : ℝ)^4563 ≤ (2062933298861/20000000000000 : ℝ)^3539 := by
    have hnat : (343462573 : ℕ)^4563*20000000000000^3539 ≤ 2062933298861^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343462573 2000000000 2062933298861 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506847867/10000000000 : ℝ)^4563 ≤ (181006481239/390625000000 : ℝ)^3539 := by
    have hnat : (5506847867 : ℕ)^4563*390625000000^3539 ≤ 181006481239^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506847867 10000000000 181006481239 390625000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307301263/2500000000 : ℝ)^4563 ≤ (43347674299733/100000000000000 : ℝ)^3539 := by
    have hnat : (1307301263 : ℕ)^4563*100000000000000^3539 ≤ 43347674299733^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307301263 2500000000 43347674299733 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343462573/2000000000 : ℝ), (5506847867/10000000000 : ℝ), (1307301263/2500000000 : ℝ)] ![(2062933298861/20000000000000 : ℝ), (181006481239/390625000000 : ℝ), (43347674299733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343462573/2000000000 : ℝ)|^4563 ≤ (2062933298861/20000000000000 : ℝ)^3539
        have hw : |(-343462573/2000000000 : ℝ)|=(343462573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506847867/10000000000 : ℝ)|^4563 ≤ (181006481239/390625000000 : ℝ)^3539
        have hw : |(5506847867/10000000000 : ℝ)|=(5506847867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307301263/2500000000 : ℝ)|^4563 ≤ (43347674299733/100000000000000 : ℝ)^3539
        have hw : |(1307301263/2500000000 : ℝ)|=(1307301263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_13 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078022073/2000000000 : ℝ)*x 0 + (-93910957/500000000 : ℝ)*x 1 + (326825289/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078022073/2000000000 : ℝ)^4563 ≤ (2817190330687/6250000000000 : ℝ)^3539 := by
    have hnat : (1078022073 : ℕ)^4563*6250000000000^3539 ≤ 2817190330687^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078022073 2000000000 2817190330687 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93910957/500000000 : ℝ)^4563 ≤ (11577284962489/100000000000000 : ℝ)^3539 := by
    have hnat : (93910957 : ℕ)^4563*100000000000000^3539 ≤ 11577284962489^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93910957 500000000 11577284962489 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326825289/625000000 : ℝ)^4563 ≤ (43347669725231/100000000000000 : ℝ)^3539 := by
    have hnat : (326825289 : ℕ)^4563*100000000000000^3539 ≤ 43347669725231^3539*625000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326825289 625000000 43347669725231 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078022073/2000000000 : ℝ), (-93910957/500000000 : ℝ), (326825289/625000000 : ℝ)] ![(2817190330687/6250000000000 : ℝ), (11577284962489/100000000000000 : ℝ), (43347669725231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078022073/2000000000 : ℝ)|^4563 ≤ (2817190330687/6250000000000 : ℝ)^3539
        have hw : |(1078022073/2000000000 : ℝ)|=(1078022073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93910957/500000000 : ℝ)|^4563 ≤ (11577284962489/100000000000000 : ℝ)^3539
        have hw : |(-93910957/500000000 : ℝ)|=(93910957/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326825289/625000000 : ℝ)|^4563 ≤ (43347669725231/100000000000000 : ℝ)^3539
        have hw : |(326825289/625000000 : ℝ)|=(326825289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_14 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390109863/10000000000 : ℝ)*x 0 + (653650583/1250000000 : ℝ)*x 1 + (-234777471/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390109863/10000000000 : ℝ)^4563 ≤ (9015007975663/20000000000000 : ℝ)^3539 := by
    have hnat : (5390109863 : ℕ)^4563*20000000000000^3539 ≤ 9015007975663^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390109863 10000000000 9015007975663 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653650583/1250000000 : ℝ)^4563 ≤ (21673835076377/50000000000000 : ℝ)^3539 := by
    have hnat : (653650583 : ℕ)^4563*50000000000000^3539 ≤ 21673835076377^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653650583 1250000000 21673835076377 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234777471/1250000000 : ℝ)^4563 ≤ (11577289953517/100000000000000 : ℝ)^3539 := by
    have hnat : (234777471 : ℕ)^4563*100000000000000^3539 ≤ 11577289953517^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234777471 1250000000 11577289953517 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390109863/10000000000 : ℝ), (653650583/1250000000 : ℝ), (-234777471/1250000000 : ℝ)] ![(9015007975663/20000000000000 : ℝ), (21673835076377/50000000000000 : ℝ), (11577289953517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390109863/10000000000 : ℝ)|^4563 ≤ (9015007975663/20000000000000 : ℝ)^3539
        have hw : |(5390109863/10000000000 : ℝ)|=(5390109863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653650583/1250000000 : ℝ)|^4563 ≤ (21673835076377/50000000000000 : ℝ)^3539
        have hw : |(653650583/1250000000 : ℝ)|=(653650583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234777471/1250000000 : ℝ)|^4563 ≤ (11577289953517/100000000000000 : ℝ)^3539
        have hw : |(-234777471/1250000000 : ℝ)|=(234777471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_box_15 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2007713783/5000000000 : ℝ)*x 0 + (1097168699/2500000000 : ℝ)*x 1 + (4388675363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007713783/5000000000 : ℝ)^4563 ≤ (15418519563963/50000000000000 : ℝ)^3539 := by
    have hnat : (2007713783 : ℕ)^4563*50000000000000^3539 ≤ 15418519563963^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007713783 5000000000 15418519563963 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097168699/2500000000 : ℝ)^4563 ≤ (17290738772249/50000000000000 : ℝ)^3539 := by
    have hnat : (1097168699 : ℕ)^4563*50000000000000^3539 ≤ 17290738772249^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097168699 2500000000 17290738772249 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388675363/10000000000 : ℝ)^4563 ≤ (34581483305037/100000000000000 : ℝ)^3539 := by
    have hnat : (4388675363 : ℕ)^4563*100000000000000^3539 ≤ 34581483305037^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388675363 10000000000 34581483305037 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2007713783/5000000000 : ℝ), (1097168699/2500000000 : ℝ), (4388675363/10000000000 : ℝ)] ![(15418519563963/50000000000000 : ℝ), (17290738772249/50000000000000 : ℝ), (34581483305037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2007713783/5000000000 : ℝ)|^4563 ≤ (15418519563963/50000000000000 : ℝ)^3539
        have hw : |(2007713783/5000000000 : ℝ)|=(2007713783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097168699/2500000000 : ℝ)|^4563 ≤ (17290738772249/50000000000000 : ℝ)^3539
        have hw : |(1097168699/2500000000 : ℝ)|=(1097168699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4388675363/10000000000 : ℝ)|^4563 ≤ (34581483305037/100000000000000 : ℝ)^3539
        have hw : |(4388675363/10000000000 : ℝ)|=(4388675363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63769/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58727/100000 : ℝ) ∧ (40271/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10767/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2199/20000 : ℝ) ^ (4561/1024 : ℝ) ≤ (5362733215463437/100000000000000000000 : ℝ) := by
    have hpowers : (2199/20000 : ℝ)^4561 ≤ (5362733215463437/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2199 : ℕ)^4561*100000000000000000000^1024 ≤ 5362733215463437^1024*20000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2199 20000 5362733215463437 100000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2199/20000 : ℝ)) (X := (5362733215463437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4561/1024 : ℝ) ≤ (24640943274298831/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4561 ≤ (24640943274298831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4561*100000000000000000000^1024 ≤ 24640943274298831^1024*25000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 24640943274298831 100000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (24640943274298831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005362733215463437/50000000000000000000 : ℝ) ≤ (10000240789758947/10000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50005362733215463437/50000000000000000000 : ℝ)^1024 ≤ (10000240789758947/10000000000000000 : ℝ)^4561 := by
      have hnat : (50005362733215463437 : ℕ)^1024*10000000000000000^4561 ≤ 10000240789758947^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005362733215463437 50000000000000000000 10000240789758947 10000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000240789758947/10000000000000000 : ℝ)) (X := (50005362733215463437/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007500919122440567/25000000000000000000 : ℝ) ≤ (5000336770346813/5000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (25007500919122440567/25000000000000000000 : ℝ)^1024 ≤ (5000336770346813/5000000000000000 : ℝ)^4561 := by
      have hnat : (25007500919122440567 : ℕ)^1024*5000000000000000^4561 ≤ 5000336770346813^4561*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007500919122440567 25000000000000000000 5000336770346813 5000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000336770346813/5000000000000000 : ℝ)) (X := (25007500919122440567/25000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024640943274298831/50000000000000000000 : ℝ) ≤ (2000221258325661/2000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50024640943274298831/50000000000000000000 : ℝ)^1024 ≤ (2000221258325661/2000000000000000 : ℝ)^4561 := by
      have hnat : (50024640943274298831 : ℕ)^1024*2000000000000000^4561 ≤ 2000221258325661^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024640943274298831 50000000000000000000 2000221258325661 2000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221258325661/2000000000000000 : ℝ)) (X := (50024640943274298831/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5362733215463437/100000000000000000000 : ℝ) ≤ ((44881564712174321873/44890000000000000000 : ℝ)+2*(432750934679/448900000000000 : ℝ)*(2199/20000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (44881564712174321873/44890000000000000000 : ℝ)+2*(432750934679/448900000000000 : ℝ)*(2199/20000 : ℝ)=(10000240789758947/10000000000000000 : ℝ) by norm_num, show 1+2*(5362733215463437/100000000000000000000 : ℝ)=(50005362733215463437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24640943274298831/100000000000000000000 : ℝ)+(5362733215463437/100000000000000000000 : ℝ) ≤ ((44881564712174321873/44890000000000000000 : ℝ)+(432750934679/448900000000000 : ℝ)*((3871/25000 : ℝ)+(2199/20000 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (44881564712174321873/44890000000000000000 : ℝ)+(432750934679/448900000000000 : ℝ)*((3871/25000 : ℝ)+(2199/20000 : ℝ))=(5000336770346813/5000000000000000 : ℝ) by norm_num, show 1+(24640943274298831/100000000000000000000 : ℝ)+(5362733215463437/100000000000000000000 : ℝ)=(25007500919122440567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24640943274298831/100000000000000000000 : ℝ) ≤ ((44881564712174321873/44890000000000000000 : ℝ)+2*(432750934679/448900000000000 : ℝ)*(3871/25000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (44881564712174321873/44890000000000000000 : ℝ)+2*(432750934679/448900000000000 : ℝ)*(3871/25000 : ℝ)=(2000221258325661/2000000000000000 : ℝ) by norm_num, show 1+2*(24640943274298831/100000000000000000000 : ℝ)=(50024640943274298831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44881564712174321873/44890000000000000000 : ℝ)*(X 1 0+X 2 0)+(432750934679/448900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44881564712174321873/44890000000000000000 : ℝ)) (alpha := (432750934679/448900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44881564712174321873/44890000000000000000 : ℝ)*(X 0 1+X 2 1)+(432750934679/448900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44881564712174321873/44890000000000000000 : ℝ)) (alpha := (432750934679/448900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44881564712174321873/44890000000000000000 : ℝ)*(X 0 2+X 1 2)+(432750934679/448900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (44881564712174321873/44890000000000000000 : ℝ)) (alpha := (432750934679/448900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65099603/400000000 : ℝ)*X 0 0+(675070691/1250000000 : ℝ)*X 0 1+(270028247/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317749017/2500000000 : ℝ)*X 1 0+(-361474499/2000000000 : ℝ)*X 1 1+(5400566019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270996479/10000000000 : ℝ)*X 2 0+(5400565579/10000000000 : ℝ)*X 2 1+(-903686269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2231117613/5000000000 : ℝ)*X 0 0+(208293499/500000000 : ℝ)*X 0 1+(2082935121/5000000000 : ℝ)*X 0 2+(2231117613/5000000000 : ℝ)*X 1 0+(208293499/500000000 : ℝ)*X 1 1+(2082935121/5000000000 : ℝ)*X 1 2+(2231117613/5000000000 : ℝ)*X 2 0+(208293499/500000000 : ℝ)*X 2 1+(2082935121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1026399921/5000000000 : ℝ)*X 0 0+(2622122047/5000000000 : ℝ)*X 0 1+(2622122663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379656329/10000000000 : ℝ)*X 1 0+(-1872160333/10000000000 : ℝ)*X 1 1+(5244244653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1344913937/2500000000 : ℝ)*X 2 0+(5244244479/10000000000 : ℝ)*X 2 1+(-468040339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((811085809/2000000000 : ℝ)*X 0 0+(174765683/400000000 : ℝ)*X 0 1+(2184570509/5000000000 : ℝ)*X 0 2+(811085809/2000000000 : ℝ)*X 1 0+(174765683/400000000 : ℝ)*X 1 1+(2184570509/5000000000 : ℝ)*X 1 2+(811085809/2000000000 : ℝ)*X 2 0+(174765683/400000000 : ℝ)*X 2 1+(2184570509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-392563167/2000000000 : ℝ)*X 0 0+(256725189/500000000 : ℝ)*X 0 1+(338809639/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314204869/2500000000 : ℝ)*X 1 0+(-1798681339/10000000000 : ℝ)*X 1 1+(677619261/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((8410911/16000000 : ℝ)*X 2 0+(1355238583/2500000000 : ℝ)*X 2 1+(-1798681139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((564268213/1250000000 : ℝ)*X 0 0+(4139324497/10000000000 : ℝ)*X 0 1+(2069662383/5000000000 : ℝ)*X 0 2+(564268213/1250000000 : ℝ)*X 1 0+(4139324497/10000000000 : ℝ)*X 1 1+(2069662383/5000000000 : ℝ)*X 1 2+(564268213/1250000000 : ℝ)*X 2 0+(4139324497/10000000000 : ℝ)*X 2 1+(2069662383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-343462573/2000000000 : ℝ)*X 0 0+(5506847867/10000000000 : ℝ)*X 0 1+(1307301263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1078022073/2000000000 : ℝ)*X 1 0+(-93910957/500000000 : ℝ)*X 1 1+(326825289/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5390109863/10000000000 : ℝ)*X 2 0+(653650583/1250000000 : ℝ)*X 2 1+(-234777471/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2007713783/5000000000 : ℝ)*X 0 0+(1097168699/2500000000 : ℝ)*X 0 1+(4388675363/10000000000 : ℝ)*X 0 2+(2007713783/5000000000 : ℝ)*X 1 0+(1097168699/2500000000 : ℝ)*X 1 1+(4388675363/10000000000 : ℝ)*X 1 2+(2007713783/5000000000 : ℝ)*X 2 0+(1097168699/2500000000 : ℝ)*X 2 1+(4388675363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63769/100000 : ℝ) ≤ (-715614607764989862759121051167507/1122250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202291191/100000000000000 : ℝ)*(lower0) + (142173899/100000000000000 : ℝ)*(upper1) + (78217033/20000000000000 : ℝ)*(lower4) + (1127137067805451/50000000000000 : ℝ)*(major0) + (1127137067805451/50000000000000 : ℝ)*(major1) + (1127137067805451/50000000000000 : ℝ)*(major2) + (705492697/20000000000000 : ℝ)*(sp1) + (22601152921/100000000000000 : ℝ)*(sp2) + (6109540707/100000000000000 : ℝ)*(sp3) + (1582027507501361/50000000000000 : ℝ)*(sp4) + (1582030938459563/50000000000000 : ℝ)*(sp5) + (316404280322969/10000000000000 : ℝ)*(sp6) + (682866055307217/50000000000000 : ℝ)*(sp7) + (649336243/6250000000000 : ℝ)*(sp12) + (682869110077571/50000000000000 : ℝ)*(f.failure) + (3164065404382611/100000000000000 : ℝ)*(f.sum) + (32185335969901/11222500000000000000000000000 : ℝ)*base66 + (29890789158697829723/2244500000000000000000000000000000 : ℝ)*base67 + (32197333243737829723/2244500000000000000000000000000000 : ℝ)*base69 + (13403148752843829723/2244500000000000000000000000000000 : ℝ)*base71 + (43173173968693/22445000000000000000000000000 : ℝ)*base73 + (12466656596185329723/2244500000000000000000000000000000 : ℝ)*base75 + (17782846439741329723/2244500000000000000000000000000000 : ℝ)*base77 + (20707720404975329723/2244500000000000000000000000000000 : ℝ)*base79 + (5105903668849/11222500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3317991/5000000000000000000000 : ℝ)*base89 + (3317991/5000000000000000000000 : ℝ)*base91 + (3317991/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58727/100000 : ℝ) ≤ (1318177592728579765950983220298761/2244500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87816867/50000000000000 : ℝ)*(upper0) + (9596381/100000000000000 : ℝ)*(upper2) + (149647339/100000000000000 : ℝ)*(upper3) + (68800529/50000000000000 : ℝ)*(upper4) + (2331950978091981/100000000000000 : ℝ)*(major0) + (2331950978091981/100000000000000 : ℝ)*(major1) + (2331950978091981/100000000000000 : ℝ)*(major2) + (100985227654379/3125000000000 : ℝ)*(sp0) + (807878638137597/25000000000000 : ℝ)*(sp1) + (161575749760149/5000000000000 : ℝ)*(sp2) + (1412795622218643/100000000000000 : ℝ)*(sp3) + (636619487/5000000000000 : ℝ)*(sp5) + (3072434287/25000000000000 : ℝ)*(sp6) + (2638648287/100000000000000 : ℝ)*(sp11) + (141279826086693/10000000000000 : ℝ)*(f.failure) + (100985227654379/3125000000000 : ℝ)*(f.sum) + (62934513648771/22445000000000000000000000000 : ℝ)*base66 + (17346685230497100413/4489000000000000000000000000000000 : ℝ)*base67 + (14586617129547899587/4489000000000000000000000000000000 : ℝ)*base70 + (3486741302314100413/4489000000000000000000000000000000 : ℝ)*base71 + (12434014397989/5611250000000000000000000000 : ℝ)*base74 + (13024264492444100413/4489000000000000000000000000000000 : ℝ)*base75 + (25746054409605899587/4489000000000000000000000000000000 : ℝ)*base78 + (9061231415505100413/4489000000000000000000000000000000 : ℝ)*base79 + (50715091007301/22445000000000000000000000000 : ℝ)*base82 + (2292447/1000000000000000000000 : ℝ)*base90 + (2292447/1000000000000000000000 : ℝ)*base92 + (2292447/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40271/50000 : ℝ) ≤ (180782088449075654277202300627431/224450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040271/1562500000000 : ℝ)*(upper0) + (397853/10000000000000 : ℝ)*(upper1) + (1089939/2500000000000 : ℝ)*(upper4) + (252328607704051/10000000000000 : ℝ)*(major0) + (252328607704051/10000000000000 : ℝ)*(major1) + (252328607704051/10000000000000 : ℝ)*(major2) + (71910711/25000000000000 : ℝ)*(sp1) + (27955111639/50000000000000 : ℝ)*(sp2) + (8603679009/100000000000000 : ℝ)*(sp3) + (2494815327/100000000000000 : ℝ)*(sp4) + (1745502018280093/50000000000000 : ℝ)*(sp8) + (349100624373267/10000000000000 : ℝ)*(sp9) + (872737655288059/25000000000000 : ℝ)*(sp10) + (1528708858567729/100000000000000 : ℝ)*(sp11) + (764358731123369/50000000000000 : ℝ)*(f.failure) + (1745503265687757/50000000000000 : ℝ)*(f.sum) + (5543778672019/1122250000000000000000000000 : ℝ)*base66 + (3297554997759007523/448900000000000000000000000000000 : ℝ)*base67 + (451742267006707523/448900000000000000000000000000000 : ℝ)*base69 + (1487753323081107523/448900000000000000000000000000000 : ℝ)*base71 + (34524140985789/4489000000000000000000000000 : ℝ)*base74 + (513723002190292477/448900000000000000000000000000000 : ℝ)*base76 + (3658008697166107523/448900000000000000000000000000000 : ℝ)*base77 + (4105749812695392477/448900000000000000000000000000000 : ℝ)*base80 + (2751431863139/2244500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (17361749/5000000000000000000000 : ℝ)*base89 + (17361749/5000000000000000000000 : ℝ)*base91 + (17361749/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10767/12500 : ℝ) ≤ (-193326021097075109923190617508007/224450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304331313/100000000000000 : ℝ)*(upper3) + (261809401/100000000000000 : ℝ)*(lower4) + (106539263/50000000000000 : ℝ)*(upper5) + (256288920684147/10000000000000 : ℝ)*(major0) + (256288920684147/10000000000000 : ℝ)*(major1) + (256288920684147/10000000000000 : ℝ)*(major2) + (20741397491/100000000000000 : ℝ)*(sp4) + (40698315147/12500000000000 : ℝ)*(sp5) + (25191601047/6250000000000 : ℝ)*(sp6) + (165963445209/100000000000000 : ℝ)*(sp7) + (1800878985156089/50000000000000 : ℝ)*(sp12) + (900363281297123/25000000000000 : ℝ)*(sp13) + (900343911523229/25000000000000 : ℝ)*(sp14) + (1552544813169339/100000000000000 : ℝ)*(sp15) + (388177694153637/25000000000000 : ℝ)*(f.failure) + (3601778711709669/100000000000000 : ℝ)*(f.sum) + (7679379182883/4489000000000000000000000000 : ℝ)*base65 + (1001442878123352669/448900000000000000000000000000000 : ℝ)*base68 + (1615868981167152669/448900000000000000000000000000000 : ℝ)*base70 + (1286223136582952669/448900000000000000000000000000000 : ℝ)*base72 + (26386065028467/4489000000000000000000000000 : ℝ)*base73 + (517457067008247331/448900000000000000000000000000000 : ℝ)*base75 + (1348655484210952669/448900000000000000000000000000000 : ℝ)*base78 + (837305411423847331/448900000000000000000000000000000 : ℝ)*base79 + (4861820169387/897800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3190623/2500000000000000000000 : ℝ)*base90 + (3190623/2500000000000000000000 : ℝ)*base92 + (3190623/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1533_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63769/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58727/100000 : ℝ) else (40271/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10767/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1533_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1533_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63769/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58727/100000 : ℝ) else (40271/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10767/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1533_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1533_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63769/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58727/100000 : ℝ) else (40271/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10767/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1533_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
