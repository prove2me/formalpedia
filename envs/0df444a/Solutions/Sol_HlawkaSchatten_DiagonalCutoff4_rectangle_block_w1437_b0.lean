-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1437_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:56.49416+00:00
-- url     : https://prove2.me/submissions/b0c51ec2-e93e-4b26-a31d-1c5b89e098bd

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
theorem support_rectangle_w1437_s0_0 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1754293367/10000000000 : ℝ)*x 0 + (5956886639/10000000000 : ℝ)*x 1 + (75516627/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1754293367/10000000000 : ℝ)^4397 ≤ (10342398020137/100000000000000 : ℝ)^3373 := by
    have hnat : (1754293367 : ℕ)^4397*100000000000000^3373 ≤ 10342398020137^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754293367 10000000000 10342398020137 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5956886639/10000000000 : ℝ)^4397 ≤ (3181252037353/6250000000000 : ℝ)^3373 := by
    have hnat : (5956886639 : ℕ)^4397*6250000000000^3373 ≤ 3181252037353^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956886639 10000000000 3181252037353 6250000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75516627/156250000 : ℝ)^4397 ≤ (38757569373303/100000000000000 : ℝ)^3373 := by
    have hnat : (75516627 : ℕ)^4397*100000000000000^3373 ≤ 38757569373303^3373*156250000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75516627 156250000 38757569373303 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1754293367/10000000000 : ℝ), (5956886639/10000000000 : ℝ), (75516627/156250000 : ℝ)] ![(10342398020137/100000000000000 : ℝ), (3181252037353/6250000000000 : ℝ), (38757569373303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1754293367/10000000000 : ℝ)|^4397 ≤ (10342398020137/100000000000000 : ℝ)^3373
        have hw : |(-1754293367/10000000000 : ℝ)|=(1754293367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5956886639/10000000000 : ℝ)|^4397 ≤ (3181252037353/6250000000000 : ℝ)^3373
        have hw : |(5956886639/10000000000 : ℝ)|=(5956886639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75516627/156250000 : ℝ)|^4397 ≤ (38757569373303/100000000000000 : ℝ)^3373
        have hw : |(75516627/156250000 : ℝ)|=(75516627/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s0_1 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (219648397/400000000 : ℝ)*x 0 + (-149299121/625000000 : ℝ)*x 1 + (4833064291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219648397/400000000 : ℝ)^4397 ≤ (45775655194883/100000000000000 : ℝ)^3373 := by
    have hnat : (219648397 : ℕ)^4397*100000000000000^3373 ≤ 45775655194883^3373*400000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219648397 400000000 45775655194883 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149299121/625000000 : ℝ)^4397 ≤ (15466773721847/100000000000000 : ℝ)^3373 := by
    have hnat : (149299121 : ℕ)^4397*100000000000000^3373 ≤ 15466773721847^3373*625000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149299121 625000000 15466773721847 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4833064291/10000000000 : ℝ)^4397 ≤ (4844696384659/12500000000000 : ℝ)^3373 := by
    have hnat : (4833064291 : ℕ)^4397*12500000000000^3373 ≤ 4844696384659^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833064291 10000000000 4844696384659 12500000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(219648397/400000000 : ℝ), (-149299121/625000000 : ℝ), (4833064291/10000000000 : ℝ)] ![(45775655194883/100000000000000 : ℝ), (15466773721847/100000000000000 : ℝ), (4844696384659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(219648397/400000000 : ℝ)|^4397 ≤ (45775655194883/100000000000000 : ℝ)^3373
        have hw : |(219648397/400000000 : ℝ)|=(219648397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149299121/625000000 : ℝ)|^4397 ≤ (15466773721847/100000000000000 : ℝ)^3373
        have hw : |(-149299121/625000000 : ℝ)|=(149299121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4833064291/10000000000 : ℝ)|^4397 ≤ (4844696384659/12500000000000 : ℝ)^3373
        have hw : |(4833064291/10000000000 : ℝ)|=(4833064291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s0_2 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2745605021/5000000000 : ℝ)*x 0 + (48330643/100000000 : ℝ)*x 1 + (-2388785773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745605021/5000000000 : ℝ)^4397 ≤ (45775656466313/100000000000000 : ℝ)^3373 := by
    have hnat : (2745605021 : ℕ)^4397*100000000000000^3373 ≤ 45775656466313^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745605021 5000000000 45775656466313 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48330643/100000000 : ℝ)^4397 ≤ (9689392792839/25000000000000 : ℝ)^3373 := by
    have hnat : (48330643 : ℕ)^4397*25000000000000^3373 ≤ 9689392792839^3373*100000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48330643 100000000 9689392792839 25000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388785773/10000000000 : ℝ)^4397 ≤ (15466772346063/100000000000000 : ℝ)^3373 := by
    have hnat : (2388785773 : ℕ)^4397*100000000000000^3373 ≤ 15466772346063^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388785773 10000000000 15466772346063 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745605021/5000000000 : ℝ), (48330643/100000000 : ℝ), (-2388785773/10000000000 : ℝ)] ![(45775656466313/100000000000000 : ℝ), (9689392792839/25000000000000 : ℝ), (15466772346063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745605021/5000000000 : ℝ)|^4397 ≤ (45775656466313/100000000000000 : ℝ)^3373
        have hw : |(2745605021/5000000000 : ℝ)|=(2745605021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48330643/100000000 : ℝ)|^4397 ≤ (9689392792839/25000000000000 : ℝ)^3373
        have hw : |(48330643/100000000 : ℝ)|=(48330643/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2388785773/10000000000 : ℝ)|^4397 ≤ (15466772346063/100000000000000 : ℝ)^3373
        have hw : |(-2388785773/10000000000 : ℝ)|=(2388785773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s0_3 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2082427727/5000000000 : ℝ)*x 0 + (775792109/2500000000 : ℝ)*x 1 + (2770749903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082427727/5000000000 : ℝ)^4397 ≤ (31923852826333/100000000000000 : ℝ)^3373 := by
    have hnat : (2082427727 : ℕ)^4397*100000000000000^3373 ≤ 31923852826333^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082427727 5000000000 31923852826333 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775792109/2500000000 : ℝ)^4397 ≤ (5438309377487/25000000000000 : ℝ)^3373 := by
    have hnat : (775792109 : ℕ)^4397*25000000000000^3373 ≤ 5438309377487^3373*2500000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775792109 2500000000 5438309377487 25000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2770749903/5000000000 : ℝ)^4397 ≤ (23161454821003/50000000000000 : ℝ)^3373 := by
    have hnat : (2770749903 : ℕ)^4397*50000000000000^3373 ≤ 23161454821003^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770749903 5000000000 23161454821003 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082427727/5000000000 : ℝ), (775792109/2500000000 : ℝ), (2770749903/5000000000 : ℝ)] ![(31923852826333/100000000000000 : ℝ), (5438309377487/25000000000000 : ℝ), (23161454821003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082427727/5000000000 : ℝ)|^4397 ≤ (31923852826333/100000000000000 : ℝ)^3373
        have hw : |(2082427727/5000000000 : ℝ)|=(2082427727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(775792109/2500000000 : ℝ)|^4397 ≤ (5438309377487/25000000000000 : ℝ)^3373
        have hw : |(775792109/2500000000 : ℝ)|=(775792109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2770749903/5000000000 : ℝ)|^4397 ≤ (23161454821003/50000000000000 : ℝ)^3373
        have hw : |(2770749903/5000000000 : ℝ)|=(2770749903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s0_4 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-439568057/2500000000 : ℝ)*x 0 + (2430900213/5000000000 : ℝ)*x 1 + (2315283/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439568057/2500000000 : ℝ)^4397 ≤ (10372987164697/100000000000000 : ℝ)^3373 := by
    have hnat : (439568057 : ℕ)^4397*100000000000000^3373 ≤ 10372987164697^3373*2500000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439568057 2500000000 10372987164697 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2430900213/5000000000 : ℝ)^4397 ≤ (39058243575039/100000000000000 : ℝ)^3373 := by
    have hnat : (2430900213 : ℕ)^4397*100000000000000^3373 ≤ 39058243575039^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430900213 5000000000 39058243575039 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2315283/3906250 : ℝ)^4397 ≤ (12642192309017/25000000000000 : ℝ)^3373 := by
    have hnat : (2315283 : ℕ)^4397*25000000000000^3373 ≤ 12642192309017^3373*3906250^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315283 3906250 12642192309017 25000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439568057/2500000000 : ℝ), (2430900213/5000000000 : ℝ), (2315283/3906250 : ℝ)] ![(10372987164697/100000000000000 : ℝ), (39058243575039/100000000000000 : ℝ), (12642192309017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439568057/2500000000 : ℝ)|^4397 ≤ (10372987164697/100000000000000 : ℝ)^3373
        have hw : |(-439568057/2500000000 : ℝ)|=(439568057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2430900213/5000000000 : ℝ)|^4397 ≤ (39058243575039/100000000000000 : ℝ)^3373
        have hw : |(2430900213/5000000000 : ℝ)|=(2430900213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2315283/3906250 : ℝ)|^4397 ≤ (12642192309017/25000000000000 : ℝ)^3373
        have hw : |(2315283/3906250 : ℝ)|=(2315283/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s0_5 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296109667/2500000000 : ℝ)*x 0 + (-161840661/1250000000 : ℝ)*x 1 + (118542491/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296109667/2500000000 : ℝ)^4397 ≤ (8494128085377/20000000000000 : ℝ)^3373 := by
    have hnat : (1296109667 : ℕ)^4397*20000000000000^3373 ≤ 8494128085377^3373*2500000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296109667 2500000000 8494128085377 20000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161840661/1250000000 : ℝ)^4397 ≤ (3480294771583/50000000000000 : ℝ)^3373 := by
    have hnat : (161840661 : ℕ)^4397*50000000000000^3373 ≤ 3480294771583^3373*1250000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161840661 1250000000 3480294771583 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118542491/200000000 : ℝ)^4397 ≤ (50568770014601/100000000000000 : ℝ)^3373 := by
    have hnat : (118542491 : ℕ)^4397*100000000000000^3373 ≤ 50568770014601^3373*200000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118542491 200000000 50568770014601 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296109667/2500000000 : ℝ), (-161840661/1250000000 : ℝ), (118542491/200000000 : ℝ)] ![(8494128085377/20000000000000 : ℝ), (3480294771583/50000000000000 : ℝ), (50568770014601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296109667/2500000000 : ℝ)|^4397 ≤ (8494128085377/20000000000000 : ℝ)^3373
        have hw : |(1296109667/2500000000 : ℝ)|=(1296109667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161840661/1250000000 : ℝ)|^4397 ≤ (3480294771583/50000000000000 : ℝ)^3373
        have hw : |(-161840661/1250000000 : ℝ)|=(161840661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118542491/200000000 : ℝ)|^4397 ≤ (50568770014601/100000000000000 : ℝ)^3373
        have hw : |(118542491/200000000 : ℝ)|=(118542491/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s0_6 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184438693/10000000000 : ℝ)*x 0 + (2963562197/5000000000 : ℝ)*x 1 + (-647362749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184438693/10000000000 : ℝ)^4397 ≤ (21235320346929/50000000000000 : ℝ)^3373 := by
    have hnat : (5184438693 : ℕ)^4397*50000000000000^3373 ≤ 21235320346929^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184438693 10000000000 21235320346929 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963562197/5000000000 : ℝ)^4397 ≤ (25284384139793/50000000000000 : ℝ)^3373 := by
    have hnat : (2963562197 : ℕ)^4397*50000000000000^3373 ≤ 25284384139793^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963562197 5000000000 25284384139793 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647362749/5000000000 : ℝ)^4397 ≤ (3480295507447/50000000000000 : ℝ)^3373 := by
    have hnat : (647362749 : ℕ)^4397*50000000000000^3373 ≤ 3480295507447^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647362749 5000000000 3480295507447 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184438693/10000000000 : ℝ), (2963562197/5000000000 : ℝ), (-647362749/5000000000 : ℝ)] ![(21235320346929/50000000000000 : ℝ), (25284384139793/50000000000000 : ℝ), (3480295507447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184438693/10000000000 : ℝ)|^4397 ≤ (21235320346929/50000000000000 : ℝ)^3373
        have hw : |(5184438693/10000000000 : ℝ)|=(5184438693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963562197/5000000000 : ℝ)|^4397 ≤ (25284384139793/50000000000000 : ℝ)^3373
        have hw : |(2963562197/5000000000 : ℝ)|=(2963562197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-647362749/5000000000 : ℝ)|^4397 ≤ (3480295507447/50000000000000 : ℝ)^3373
        have hw : |(-647362749/5000000000 : ℝ)|=(647362749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s0_7 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173489881/10000000000 : ℝ)*x 0 + (5479151617/10000000000 : ℝ)*x 1 + (3167742667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173489881/10000000000 : ℝ)^4397 ≤ (32010155767287/100000000000000 : ℝ)^3373 := by
    have hnat : (4173489881 : ℕ)^4397*100000000000000^3373 ≤ 32010155767287^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173489881 10000000000 32010155767287 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479151617/10000000000 : ℝ)^4397 ≤ (22822331086823/50000000000000 : ℝ)^3373 := by
    have hnat : (5479151617 : ℕ)^4397*50000000000000^3373 ≤ 22822331086823^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479151617 10000000000 22822331086823 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167742667/10000000000 : ℝ)^4397 ≤ (893807281667/4000000000000 : ℝ)^3373 := by
    have hnat : (3167742667 : ℕ)^4397*4000000000000^3373 ≤ 893807281667^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167742667 10000000000 893807281667 4000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173489881/10000000000 : ℝ), (5479151617/10000000000 : ℝ), (3167742667/10000000000 : ℝ)] ![(32010155767287/100000000000000 : ℝ), (22822331086823/50000000000000 : ℝ), (893807281667/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173489881/10000000000 : ℝ)|^4397 ≤ (32010155767287/100000000000000 : ℝ)^3373
        have hw : |(4173489881/10000000000 : ℝ)|=(4173489881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479151617/10000000000 : ℝ)|^4397 ≤ (22822331086823/50000000000000 : ℝ)^3373
        have hw : |(5479151617/10000000000 : ℝ)|=(5479151617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167742667/10000000000 : ℝ)|^4397 ≤ (893807281667/4000000000000 : ℝ)^3373
        have hw : |(3167742667/10000000000 : ℝ)|=(3167742667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1437_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (263/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26203/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (1099/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1099 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1099*1^256 ≤ 0^256*1^1099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1099 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1099/256 : ℝ) ≤ (978646805311285179/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1099 ≤ (978646805311285179/50000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1099*50000000000000000000^256 ≤ 978646805311285179^256*5^1099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 978646805311285179 50000000000000000000 1099 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (978646805311285179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1099 := by
      have hnat : (1 : ℕ)^256*1^1099 ≤ 1^1099*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50978646805311285179/50000000000000000000 : ℝ) ≤ (1255656830422453/1250000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (50978646805311285179/50000000000000000000 : ℝ)^256 ≤ (1255656830422453/1250000000000000 : ℝ)^1099 := by
      have hnat : (50978646805311285179 : ℕ)^256*1250000000000000^1099 ≤ 1255656830422453^1099*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50978646805311285179 50000000000000000000 1255656830422453 1250000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255656830422453/1250000000000000 : ℝ)) (X := (50978646805311285179/50000000000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25978646805311285179/25000000000000000000 : ℝ) ≤ (630656830422453/625000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (25978646805311285179/25000000000000000000 : ℝ)^256 ≤ (630656830422453/625000000000000 : ℝ)^1099 := by
      have hnat : (25978646805311285179 : ℕ)^256*625000000000000^1099 ≤ 630656830422453^1099*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25978646805311285179 25000000000000000000 630656830422453 625000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (630656830422453/625000000000000 : ℝ)) (X := (25978646805311285179/25000000000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5656830422453/500000000000000 : ℝ)*(0 : ℝ))^(1099/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(5656830422453/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(978646805311285179/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5656830422453/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1099/256 : ℝ) := by
    rw [show (1 : ℝ)+(5656830422453/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1255656830422453/1250000000000000 : ℝ) by norm_num, show 1+(978646805311285179/50000000000000000000 : ℝ)+(0 : ℝ)=(50978646805311285179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(978646805311285179/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5656830422453/500000000000000 : ℝ)*(2/5 : ℝ))^(1099/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(5656830422453/500000000000000 : ℝ)*(2/5 : ℝ)=(630656830422453/625000000000000 : ℝ) by norm_num, show 1+2*(978646805311285179/50000000000000000000 : ℝ)=(25978646805311285179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5656830422453/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5656830422453/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5656830422453/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5656830422453/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5656830422453/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5656830422453/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1754293367/10000000000 : ℝ)*X 0 0+(5956886639/10000000000 : ℝ)*X 0 1+(75516627/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((219648397/400000000 : ℝ)*X 1 0+(-149299121/625000000 : ℝ)*X 1 1+(4833064291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2745605021/5000000000 : ℝ)*X 2 0+(48330643/100000000 : ℝ)*X 2 1+(-2388785773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2082427727/5000000000 : ℝ)*X 0 0+(775792109/2500000000 : ℝ)*X 0 1+(2770749903/5000000000 : ℝ)*X 0 2+(2082427727/5000000000 : ℝ)*X 1 0+(775792109/2500000000 : ℝ)*X 1 1+(2770749903/5000000000 : ℝ)*X 1 2+(2082427727/5000000000 : ℝ)*X 2 0+(775792109/2500000000 : ℝ)*X 2 1+(2770749903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-439568057/2500000000 : ℝ)*X 0 0+(2430900213/5000000000 : ℝ)*X 0 1+(2315283/3906250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1296109667/2500000000 : ℝ)*X 1 0+(-161840661/1250000000 : ℝ)*X 1 1+(118542491/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184438693/10000000000 : ℝ)*X 2 0+(2963562197/5000000000 : ℝ)*X 2 1+(-647362749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4173489881/10000000000 : ℝ)*X 0 0+(5479151617/10000000000 : ℝ)*X 0 1+(3167742667/10000000000 : ℝ)*X 0 2+(4173489881/10000000000 : ℝ)*X 1 0+(5479151617/10000000000 : ℝ)*X 1 1+(3167742667/10000000000 : ℝ)*X 1 2+(4173489881/10000000000 : ℝ)*X 2 0+(5479151617/10000000000 : ℝ)*X 2 1+(3167742667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118308532863693000159579/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22885501/2000000000000 : ℝ)*(base19) + (1137206173/100000000000000 : ℝ)*(base23) + (71105687/50000000000000 : ℝ)*(upper3) + (7146323/50000000000000 : ℝ)*(upper4) + (168346437/100000000000000 : ℝ)*(upper5) + (649974292138419/100000000000000 : ℝ)*(major0) + (649974292138419/100000000000000 : ℝ)*(major1) + (649974292138419/100000000000000 : ℝ)*(major2) + (55613998981101/6250000000000 : ℝ)*(sp0) + (889827076230769/100000000000000 : ℝ)*(sp1) + (444913541649823/50000000000000 : ℝ)*(sp2) + (410118346844673/100000000000000 : ℝ)*(sp3) + (4236808203/100000000000000 : ℝ)*(sp4) + (1859181631/100000000000000 : ℝ)*(sp7) + (6408128219161/1562500000000 : ℝ)*(f.failure) + (889828220505819/100000000000000 : ℝ)*(f.sum) + (71973305903193/25000000000000000000000000000 : ℝ)*base66 + (139158271328193/50000000000000000000000000000 : ℝ)*base68 + (256497941371807/50000000000000000000000000000 : ℝ)*base69 + (251494217378193/50000000000000000000000000000 : ℝ)*base72 + (3362922246807/25000000000000000000000000000 : ℝ)*base73 + (117770866821807/50000000000000000000000000000 : ℝ)*base75 + (65847357728193/50000000000000000000000000000 : ℝ)*base78 + (36192193771807/50000000000000000000000000000 : ℝ)*base79 + (109832347596807/25000000000000000000000000000 : ℝ)*base81 + (12753/3125000000000000000 : ℝ)*base90 + (12753/3125000000000000000 : ℝ)*base92 + (12753/3125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1489942600620678429/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (136066397/10000000000000 : ℝ)*(base19) + (1371897357/100000000000000 : ℝ)*(base23) + (142005661/100000000000000 : ℝ)*(base32) + (206812011/100000000000000 : ℝ)*(upper3) + (118266207/100000000000000 : ℝ)*(upper5) + (342829356755699/50000000000000 : ℝ)*(major0) + (342829356755699/50000000000000 : ℝ)*(major1) + (342829356755699/50000000000000 : ℝ)*(major2) + (3235107393/100000000000000 : ℝ)*(sp1) + (1674227039/50000000000000 : ℝ)*(sp2) + (938680897588493/100000000000000 : ℝ)*(sp4) + (93867630181713/10000000000000 : ℝ)*(sp5) + (938676177237059/100000000000000 : ℝ)*(sp6) + (432636188769619/100000000000000 : ℝ)*(sp7) + (432636330775279/100000000000000 : ℝ)*(f.failure) + (938680897588493/100000000000000 : ℝ)*(f.sum) + (10506976377853/12500000000000000000000000000 : ℝ)*base66 + (89586863215353/25000000000000000000000000000 : ℝ)*base68 + (126867622484647/25000000000000000000000000000 : ℝ)*base69 + (54624092709647/25000000000000000000000000000 : ℝ)*base71 + (53647760127853/12500000000000000000000000000 : ℝ)*base74 + (135234216909647/25000000000000000000000000000 : ℝ)*base75 + (42541172759647/25000000000000000000000000000 : ℝ)*base77 + (260857728915353/25000000000000000000000000000 : ℝ)*base80 + (33629045347147/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1985117/200000000000000000000 : ℝ)*base90 + (1985117/200000000000000000000 : ℝ)*base92 + (1985117/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1437_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (263/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26203/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1437_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1437_s1_0 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7521547/39062500 : ℝ)*x 0 + (2801018959/5000000000 : ℝ)*x 1 + (5078132037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7521547/39062500 : ℝ)^4397 ≤ (1167736159931/10000000000000 : ℝ)^3373 := by
    have hnat : (7521547 : ℕ)^4397*10000000000000^3373 ≤ 1167736159931^3373*39062500^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7521547 39062500 1167736159931 10000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2801018959/5000000000 : ℝ)^4397 ≤ (5872960897431/12500000000000 : ℝ)^3373 := by
    have hnat : (2801018959 : ℕ)^4397*12500000000000^3373 ≤ 5872960897431^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801018959 5000000000 5872960897431 12500000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078132037/10000000000 : ℝ)^4397 ≤ (20669475604189/50000000000000 : ℝ)^3373 := by
    have hnat : (5078132037 : ℕ)^4397*50000000000000^3373 ≤ 20669475604189^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078132037 10000000000 20669475604189 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7521547/39062500 : ℝ), (2801018959/5000000000 : ℝ), (5078132037/10000000000 : ℝ)] ![(1167736159931/10000000000000 : ℝ), (5872960897431/12500000000000 : ℝ), (20669475604189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7521547/39062500 : ℝ)|^4397 ≤ (1167736159931/10000000000000 : ℝ)^3373
        have hw : |(-7521547/39062500 : ℝ)|=(7521547/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2801018959/5000000000 : ℝ)|^4397 ≤ (5872960897431/12500000000000 : ℝ)^3373
        have hw : |(2801018959/5000000000 : ℝ)|=(2801018959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078132037/10000000000 : ℝ)|^4397 ≤ (20669475604189/50000000000000 : ℝ)^3373
        have hw : |(5078132037/10000000000 : ℝ)|=(5078132037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s1_1 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396009129/10000000000 : ℝ)*x 0 + (-1101479301/5000000000 : ℝ)*x 1 + (101562669/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396009129/10000000000 : ℝ)^4397 ≤ (894876978243/2000000000000 : ℝ)^3373 := by
    have hnat : (5396009129 : ℕ)^4397*2000000000000^3373 ≤ 894876978243^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396009129 10000000000 894876978243 2000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101479301/5000000000 : ℝ)^4397 ≤ (13917184866679/100000000000000 : ℝ)^3373 := by
    have hnat : (1101479301 : ℕ)^4397*100000000000000^3373 ≤ 13917184866679^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101479301 5000000000 13917184866679 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101562669/200000000 : ℝ)^4397 ≤ (41338966203077/100000000000000 : ℝ)^3373 := by
    have hnat : (101562669 : ℕ)^4397*100000000000000^3373 ≤ 41338966203077^3373*200000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101562669 200000000 41338966203077 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396009129/10000000000 : ℝ), (-1101479301/5000000000 : ℝ), (101562669/200000000 : ℝ)] ![(894876978243/2000000000000 : ℝ), (13917184866679/100000000000000 : ℝ), (41338966203077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396009129/10000000000 : ℝ)|^4397 ≤ (894876978243/2000000000000 : ℝ)^3373
        have hw : |(5396009129/10000000000 : ℝ)|=(5396009129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101479301/5000000000 : ℝ)|^4397 ≤ (13917184866679/100000000000000 : ℝ)^3373
        have hw : |(-1101479301/5000000000 : ℝ)|=(1101479301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101562669/200000000 : ℝ)|^4397 ≤ (41338966203077/100000000000000 : ℝ)^3373
        have hw : |(101562669/200000000 : ℝ)|=(101562669/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s1_2 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698005133/5000000000 : ℝ)*x 0 + (5078132157/10000000000 : ℝ)*x 1 + (-275369847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698005133/5000000000 : ℝ)^4397 ≤ (8948772240483/20000000000000 : ℝ)^3373 := by
    have hnat : (2698005133 : ℕ)^4397*20000000000000^3373 ≤ 8948772240483^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698005133 5000000000 8948772240483 20000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078132157/10000000000 : ℝ)^4397 ≤ (41338952481813/100000000000000 : ℝ)^3373 := by
    have hnat : (5078132157 : ℕ)^4397*100000000000000^3373 ≤ 41338952481813^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078132157 10000000000 41338952481813 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275369847/1250000000 : ℝ)^4397 ≤ (347929657491/2500000000000 : ℝ)^3373 := by
    have hnat : (275369847 : ℕ)^4397*2500000000000^3373 ≤ 347929657491^3373*1250000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275369847 1250000000 347929657491 2500000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698005133/5000000000 : ℝ), (5078132157/10000000000 : ℝ), (-275369847/1250000000 : ℝ)] ![(8948772240483/20000000000000 : ℝ), (41338952481813/100000000000000 : ℝ), (347929657491/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698005133/5000000000 : ℝ)|^4397 ≤ (8948772240483/20000000000000 : ℝ)^3373
        have hw : |(2698005133/5000000000 : ℝ)|=(2698005133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078132157/10000000000 : ℝ)|^4397 ≤ (41338952481813/100000000000000 : ℝ)^3373
        have hw : |(5078132157/10000000000 : ℝ)|=(5078132157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275369847/1250000000 : ℝ)|^4397 ≤ (347929657491/2500000000000 : ℝ)^3373
        have hw : |(-275369847/1250000000 : ℝ)|=(275369847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s1_3 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275183193/10000000000 : ℝ)*x 0 + (1870221309/5000000000 : ℝ)*x 1 + (975429197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275183193/10000000000 : ℝ)^4397 ≤ (33030661224209/100000000000000 : ℝ)^3373 := by
    have hnat : (4275183193 : ℕ)^4397*100000000000000^3373 ≤ 33030661224209^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275183193 10000000000 33030661224209 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870221309/5000000000 : ℝ)^4397 ≤ (27750309909451/100000000000000 : ℝ)^3373 := by
    have hnat : (1870221309 : ℕ)^4397*100000000000000^3373 ≤ 27750309909451^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870221309 5000000000 27750309909451 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975429197/2000000000 : ℝ)^4397 ≤ (392190288581/1000000000000 : ℝ)^3373 := by
    have hnat : (975429197 : ℕ)^4397*1000000000000^3373 ≤ 392190288581^3373*2000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975429197 2000000000 392190288581 1000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275183193/10000000000 : ℝ), (1870221309/5000000000 : ℝ), (975429197/2000000000 : ℝ)] ![(33030661224209/100000000000000 : ℝ), (27750309909451/100000000000000 : ℝ), (392190288581/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275183193/10000000000 : ℝ)|^4397 ≤ (33030661224209/100000000000000 : ℝ)^3373
        have hw : |(4275183193/10000000000 : ℝ)|=(4275183193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1870221309/5000000000 : ℝ)|^4397 ≤ (27750309909451/100000000000000 : ℝ)^3373
        have hw : |(1870221309/5000000000 : ℝ)|=(1870221309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(975429197/2000000000 : ℝ)|^4397 ≤ (392190288581/1000000000000 : ℝ)^3373
        have hw : |(975429197/2000000000 : ℝ)|=(975429197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s1_4 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925903329/10000000000 : ℝ)*x 0 + (2542118563/5000000000 : ℝ)*x 1 + (2797914969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925903329/10000000000 : ℝ)^4397 ≤ (11680423528239/100000000000000 : ℝ)^3373 := by
    have hnat : (1925903329 : ℕ)^4397*100000000000000^3373 ≤ 11680423528239^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925903329 10000000000 11680423528239 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542118563/5000000000 : ℝ)^4397 ≤ (20701874993107/50000000000000 : ℝ)^3373 := by
    have hnat : (2542118563 : ℕ)^4397*50000000000000^3373 ≤ 20701874993107^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542118563 5000000000 20701874993107 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2797914969/5000000000 : ℝ)^4397 ≤ (46915826468211/100000000000000 : ℝ)^3373 := by
    have hnat : (2797914969 : ℕ)^4397*100000000000000^3373 ≤ 46915826468211^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797914969 5000000000 46915826468211 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925903329/10000000000 : ℝ), (2542118563/5000000000 : ℝ), (2797914969/5000000000 : ℝ)] ![(11680423528239/100000000000000 : ℝ), (20701874993107/50000000000000 : ℝ), (46915826468211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925903329/10000000000 : ℝ)|^4397 ≤ (11680423528239/100000000000000 : ℝ)^3373
        have hw : |(-1925903329/10000000000 : ℝ)|=(1925903329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542118563/5000000000 : ℝ)|^4397 ≤ (20701874993107/50000000000000 : ℝ)^3373
        have hw : |(2542118563/5000000000 : ℝ)|=(2542118563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2797914969/5000000000 : ℝ)|^4397 ≤ (46915826468211/100000000000000 : ℝ)^3373
        have hw : |(2797914969/5000000000 : ℝ)|=(2797914969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s1_5 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131476159/250000000 : ℝ)*x 0 + (-1685261649/10000000000 : ℝ)*x 1 + (5595829959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131476159/250000000 : ℝ)^4397 ≤ (1352159511081/3125000000000 : ℝ)^3373 := by
    have hnat : (131476159 : ℕ)^4397*3125000000000^3373 ≤ 1352159511081^3373*250000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131476159 250000000 1352159511081 3125000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1685261649/10000000000 : ℝ)^4397 ≤ (4907534469683/50000000000000 : ℝ)^3373 := by
    have hnat : (1685261649 : ℕ)^4397*50000000000000^3373 ≤ 4907534469683^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685261649 10000000000 4907534469683 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5595829959/10000000000 : ℝ)^4397 ≤ (91632474019/195312500000 : ℝ)^3373 := by
    have hnat : (5595829959 : ℕ)^4397*195312500000^3373 ≤ 91632474019^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595829959 10000000000 91632474019 195312500000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131476159/250000000 : ℝ), (-1685261649/10000000000 : ℝ), (5595829959/10000000000 : ℝ)] ![(1352159511081/3125000000000 : ℝ), (4907534469683/50000000000000 : ℝ), (91632474019/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131476159/250000000 : ℝ)|^4397 ≤ (1352159511081/3125000000000 : ℝ)^3373
        have hw : |(131476159/250000000 : ℝ)|=(131476159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1685261649/10000000000 : ℝ)|^4397 ≤ (4907534469683/50000000000000 : ℝ)^3373
        have hw : |(-1685261649/10000000000 : ℝ)|=(1685261649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5595829959/10000000000 : ℝ)|^4397 ≤ (91632474019/195312500000 : ℝ)^3373
        have hw : |(5595829959/10000000000 : ℝ)|=(5595829959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s1_6 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259046293/10000000000 : ℝ)*x 0 + (5595829919/10000000000 : ℝ)*x 1 + (-8426309/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259046293/10000000000 : ℝ)^4397 ≤ (21634551817997/50000000000000 : ℝ)^3373 := by
    have hnat : (5259046293 : ℕ)^4397*50000000000000^3373 ≤ 21634551817997^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259046293 10000000000 21634551817997 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595829919/10000000000 : ℝ)^4397 ≤ (46915826260553/100000000000000 : ℝ)^3373 := by
    have hnat : (5595829919 : ℕ)^4397*100000000000000^3373 ≤ 46915826260553^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595829919 10000000000 46915826260553 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8426309/50000000 : ℝ)^4397 ≤ (1226883760723/12500000000000 : ℝ)^3373 := by
    have hnat : (8426309 : ℕ)^4397*12500000000000^3373 ≤ 1226883760723^3373*50000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8426309 50000000 1226883760723 12500000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259046293/10000000000 : ℝ), (5595829919/10000000000 : ℝ), (-8426309/50000000 : ℝ)] ![(21634551817997/50000000000000 : ℝ), (46915826260553/100000000000000 : ℝ), (1226883760723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259046293/10000000000 : ℝ)|^4397 ≤ (21634551817997/50000000000000 : ℝ)^3373
        have hw : |(5259046293/10000000000 : ℝ)|=(5259046293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5595829919/10000000000 : ℝ)|^4397 ≤ (46915826260553/100000000000000 : ℝ)^3373
        have hw : |(5595829919/10000000000 : ℝ)|=(5595829919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8426309/50000000 : ℝ)|^4397 ≤ (1226883760723/12500000000000 : ℝ)^3373
        have hw : |(-8426309/50000000 : ℝ)|=(8426309/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s1_7 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069005983/2500000000 : ℝ)*x 0 + (607987649/1250000000 : ℝ)*x 1 + (3753909703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069005983/2500000000 : ℝ)^4397 ≤ (33039129145649/100000000000000 : ℝ)^3373 := by
    have hnat : (1069005983 : ℕ)^4397*100000000000000^3373 ≤ 33039129145649^3373*2500000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069005983 2500000000 33039129145649 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607987649/1250000000 : ℝ)^4397 ≤ (39080245560219/100000000000000 : ℝ)^3373 := by
    have hnat : (607987649 : ℕ)^4397*100000000000000^3373 ≤ 39080245560219^3373*1250000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607987649 1250000000 39080245560219 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3753909703/10000000000 : ℝ)^4397 ≤ (1394031264153/5000000000000 : ℝ)^3373 := by
    have hnat : (3753909703 : ℕ)^4397*5000000000000^3373 ≤ 1394031264153^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3753909703 10000000000 1394031264153 5000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069005983/2500000000 : ℝ), (607987649/1250000000 : ℝ), (3753909703/10000000000 : ℝ)] ![(33039129145649/100000000000000 : ℝ), (39080245560219/100000000000000 : ℝ), (1394031264153/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069005983/2500000000 : ℝ)|^4397 ≤ (33039129145649/100000000000000 : ℝ)^3373
        have hw : |(1069005983/2500000000 : ℝ)|=(1069005983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(607987649/1250000000 : ℝ)|^4397 ≤ (39080245560219/100000000000000 : ℝ)^3373
        have hw : |(607987649/1250000000 : ℝ)|=(607987649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3753909703/10000000000 : ℝ)|^4397 ≤ (1394031264153/5000000000000 : ℝ)^3373
        have hw : |(3753909703/10000000000 : ℝ)|=(3753909703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1437_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (263/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (7717/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18793/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (263/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (263/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (263/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (263/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26203/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (263/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26203/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (263/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (263/12500 : ℝ) ^ (1099/256 : ℝ) ≤ (49394407191/781250000000000000 : ℝ) := by
    have hpowers : (263/12500 : ℝ)^1099 ≤ (49394407191/781250000000000000 : ℝ)^256 := by
      have hnat : (263 : ℕ)^1099*781250000000000000^256 ≤ 49394407191^256*12500^1099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        263 12500 49394407191 781250000000000000 1099 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (263/12500 : ℝ)) (X := (49394407191/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26203/100000 : ℝ) ^ (1099/256 : ℝ) ≤ (318419086337071699/100000000000000000000 : ℝ) := by
    have hpowers : (26203/100000 : ℝ)^1099 ≤ (318419086337071699/100000000000000000000 : ℝ)^256 := by
      have hnat : (26203 : ℕ)^1099*100000000000000000000^256 ≤ 318419086337071699^256*100000^1099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26203 100000 318419086337071699 100000000000000000000 1099 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26203/100000 : ℝ)) (X := (318419086337071699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (390625049394407191/390625000000000000 : ℝ) ≤ (10000000294550657/10000000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (390625049394407191/390625000000000000 : ℝ)^256 ≤ (10000000294550657/10000000000000000 : ℝ)^1099 := by
      have hnat : (390625049394407191 : ℕ)^256*10000000000000000^1099 ≤ 10000000294550657^1099*390625000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390625049394407191 390625000000000000 10000000294550657 10000000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000294550657/10000000000000000 : ℝ)) (X := (390625049394407191/390625000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100318425408821192147/100000000000000000000 : ℝ) ≤ (10007408329186147/10000000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (100318425408821192147/100000000000000000000 : ℝ)^256 ≤ (10007408329186147/10000000000000000 : ℝ)^1099 := by
      have hnat : (100318425408821192147 : ℕ)^256*10000000000000000^1099 ≤ 10007408329186147^1099*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100318425408821192147 100000000000000000000 10007408329186147 10000000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007408329186147/10000000000000000 : ℝ)) (X := (100318425408821192147/100000000000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50318419086337071699/50000000000000000000 : ℝ) ≤ (10014816363821637/10000000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (50318419086337071699/50000000000000000000 : ℝ)^256 ≤ (10014816363821637/10000000000000000 : ℝ)^1099 := by
      have hnat : (50318419086337071699 : ℕ)^256*10000000000000000^1099 ≤ 10014816363821637^1099*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50318419086337071699 50000000000000000000 10014816363821637 10000000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014816363821637/10000000000000000 : ℝ)) (X := (50318419086337071699/50000000000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(49394407191/781250000000000000 : ℝ) ≤ ((240958834088630141123/240990000000000000000 : ℝ)+2*(740803463549/240990000000000 : ℝ)*(263/12500 : ℝ))^(1099/256 : ℝ) := by
    rw [show (240958834088630141123/240990000000000000000 : ℝ)+2*(740803463549/240990000000000 : ℝ)*(263/12500 : ℝ)=(10000000294550657/10000000000000000 : ℝ) by norm_num, show 1+2*(49394407191/781250000000000000 : ℝ)=(390625049394407191/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(318419086337071699/100000000000000000000 : ℝ)+(49394407191/781250000000000000 : ℝ) ≤ ((240958834088630141123/240990000000000000000 : ℝ)+(740803463549/240990000000000 : ℝ)*((26203/100000 : ℝ)+(263/12500 : ℝ)))^(1099/256 : ℝ) := by
    rw [show (240958834088630141123/240990000000000000000 : ℝ)+(740803463549/240990000000000 : ℝ)*((26203/100000 : ℝ)+(263/12500 : ℝ))=(10007408329186147/10000000000000000 : ℝ) by norm_num, show 1+(318419086337071699/100000000000000000000 : ℝ)+(49394407191/781250000000000000 : ℝ)=(100318425408821192147/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(318419086337071699/100000000000000000000 : ℝ) ≤ ((240958834088630141123/240990000000000000000 : ℝ)+2*(740803463549/240990000000000 : ℝ)*(26203/100000 : ℝ))^(1099/256 : ℝ) := by
    rw [show (240958834088630141123/240990000000000000000 : ℝ)+2*(740803463549/240990000000000 : ℝ)*(26203/100000 : ℝ)=(10014816363821637/10000000000000000 : ℝ) by norm_num, show 1+2*(318419086337071699/100000000000000000000 : ℝ)=(50318419086337071699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (240958834088630141123/240990000000000000000 : ℝ)*(X 1 0+X 2 0)+(740803463549/240990000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (263/12500 : ℝ)) (hi := (26203/100000 : ℝ)) (c := (240958834088630141123/240990000000000000000 : ℝ)) (alpha := (740803463549/240990000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (240958834088630141123/240990000000000000000 : ℝ)*(X 0 1+X 2 1)+(740803463549/240990000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (263/12500 : ℝ)) (hi := (26203/100000 : ℝ)) (c := (240958834088630141123/240990000000000000000 : ℝ)) (alpha := (740803463549/240990000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (240958834088630141123/240990000000000000000 : ℝ)*(X 0 2+X 1 2)+(740803463549/240990000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (263/12500 : ℝ)) (hi := (26203/100000 : ℝ)) (c := (240958834088630141123/240990000000000000000 : ℝ)) (alpha := (740803463549/240990000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-7521547/39062500 : ℝ)*X 0 0+(2801018959/5000000000 : ℝ)*X 0 1+(5078132037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5396009129/10000000000 : ℝ)*X 1 0+(-1101479301/5000000000 : ℝ)*X 1 1+(101562669/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2698005133/5000000000 : ℝ)*X 2 0+(5078132157/10000000000 : ℝ)*X 2 1+(-275369847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4275183193/10000000000 : ℝ)*X 0 0+(1870221309/5000000000 : ℝ)*X 0 1+(975429197/2000000000 : ℝ)*X 0 2+(4275183193/10000000000 : ℝ)*X 1 0+(1870221309/5000000000 : ℝ)*X 1 1+(975429197/2000000000 : ℝ)*X 1 2+(4275183193/10000000000 : ℝ)*X 2 0+(1870221309/5000000000 : ℝ)*X 2 1+(975429197/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1925903329/10000000000 : ℝ)*X 0 0+(2542118563/5000000000 : ℝ)*X 0 1+(2797914969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((131476159/250000000 : ℝ)*X 1 0+(-1685261649/10000000000 : ℝ)*X 1 1+(5595829959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259046293/10000000000 : ℝ)*X 2 0+(5595829919/10000000000 : ℝ)*X 2 1+(-8426309/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1069005983/2500000000 : ℝ)*X 0 0+(607987649/1250000000 : ℝ)*X 0 1+(3753909703/10000000000 : ℝ)*X 0 2+(1069005983/2500000000 : ℝ)*X 1 0+(607987649/1250000000 : ℝ)*X 1 1+(3753909703/10000000000 : ℝ)*X 1 2+(1069005983/2500000000 : ℝ)*X 2 0+(607987649/1250000000 : ℝ)*X 2 1+(3753909703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27304612555254239128255385351/4016500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45591823/4000000000000 : ℝ)*(base19) + (1532588167/100000000000000 : ℝ)*(base23) + (13198509/12500000000000 : ℝ)*(upper3) + (2537663/50000000000000 : ℝ)*(upper4) + (107176123/100000000000000 : ℝ)*(upper5) + (1394256780869363/100000000000000 : ℝ)*(major0) + (1394256780869363/100000000000000 : ℝ)*(major1) + (1394256780869363/100000000000000 : ℝ)*(major2) + (954376206912939/50000000000000 : ℝ)*(sp0) + (381753056103081/20000000000000 : ℝ)*(sp1) + (477191221930703/25000000000000 : ℝ)*(sp2) + (439870831891127/50000000000000 : ℝ)*(sp3) + (14006485101/100000000000000 : ℝ)*(sp4) + (5251041789/100000000000000 : ℝ)*(sp7) + (439873457412021/50000000000000 : ℝ)*(f.failure) + (1908766420310979/100000000000000 : ℝ)*(f.sum) + (21659656488119/24099000000000000000000000000 : ℝ)*base65 + (114022334685205885351/24099000000000000000000000000000000 : ℝ)*base68 + (6166104562585114649/24099000000000000000000000000000000 : ℝ)*base69 + (3894833240719114649/24099000000000000000000000000000000 : ℝ)*base71 + (14150021189597/3012375000000000000000000000 : ℝ)*base74 + (336825082473988885351/24099000000000000000000000000000000 : ℝ)*base76 + (10901478993766114649/24099000000000000000000000000000000 : ℝ)*base77 + (10232982807148114649/24099000000000000000000000000000000 : ℝ)*base79 + (40681003125181/24099000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (512783/100000000000000000000 : ℝ)*base90 + (512783/100000000000000000000 : ℝ)*base92 + (512783/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75658387819519567508622167/34625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23821/500000000000 : ℝ)*(base1) + (280163023/50000000000000 : ℝ)*(base19) + (525530059/100000000000000 : ℝ)*(base23) + (62999923/100000000000000 : ℝ)*(upper3) + (4624947/12500000000000 : ℝ)*(upper5) + (356948383646641/25000000000000 : ℝ)*(major0) + (356948383646641/25000000000000 : ℝ)*(major1) + (356948383646641/25000000000000 : ℝ)*(major2) + (3577695681/100000000000000 : ℝ)*(sp1) + (3197781441/100000000000000 : ℝ)*(sp2) + (488669773743249/25000000000000 : ℝ)*(sp4) + (195467495218707/10000000000000 : ℝ)*(sp5) + (122167210431081/6250000000000 : ℝ)*(sp6) + (900907901364131/100000000000000 : ℝ)*(sp7) + (900907906128331/100000000000000 : ℝ)*(f.failure) + (1954679090208797/100000000000000 : ℝ)*(f.sum) + (543395863553/602475000000000000000000000 : ℝ)*base66 + (32331569229684082157/6024750000000000000000000000000000 : ℝ)*base68 + (13264198500914167843/6024750000000000000000000000000000 : ℝ)*base69 + (10607082818385832157/6024750000000000000000000000000000 : ℝ)*base72 + (9386944954621/3012375000000000000000000000 : ℝ)*base74 + (11839159448052832157/6024750000000000000000000000000000 : ℝ)*base76 + (88690677861985417843/6024750000000000000000000000000000 : ℝ)*base77 + (41526830451867832157/6024750000000000000000000000000000 : ℝ)*base80 + (74831104850351/24099000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1819087/200000000000000000000 : ℝ)*base89 + (1819087/200000000000000000000 : ℝ)*base91 + (1819087/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1437_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (263/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7717/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18793/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1437_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1437_s2_0 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-391611499/2000000000 : ℝ)*x 0 + (5456394181/10000000000 : ℝ)*x 1 + (1040564019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391611499/2000000000 : ℝ)^4397 ≤ (1193528048419/10000000000000 : ℝ)^3373 := by
    have hnat : (391611499 : ℕ)^4397*10000000000000^3373 ≤ 1193528048419^3373*2000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391611499 2000000000 1193528048419 10000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456394181/10000000000 : ℝ)^4397 ≤ (45397679792547/100000000000000 : ℝ)^3373 := by
    have hnat : (5456394181 : ℕ)^4397*100000000000000^3373 ≤ 45397679792547^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456394181 10000000000 45397679792547 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040564019/2000000000 : ℝ)^4397 ≤ (4266703970749/10000000000000 : ℝ)^3373 := by
    have hnat : (1040564019 : ℕ)^4397*10000000000000^3373 ≤ 4266703970749^3373*2000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040564019 2000000000 4266703970749 10000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391611499/2000000000 : ℝ), (5456394181/10000000000 : ℝ), (1040564019/2000000000 : ℝ)] ![(1193528048419/10000000000000 : ℝ), (45397679792547/100000000000000 : ℝ), (4266703970749/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391611499/2000000000 : ℝ)|^4397 ≤ (1193528048419/10000000000000 : ℝ)^3373
        have hw : |(-391611499/2000000000 : ℝ)|=(391611499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456394181/10000000000 : ℝ)|^4397 ≤ (45397679792547/100000000000000 : ℝ)^3373
        have hw : |(5456394181/10000000000 : ℝ)|=(5456394181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040564019/2000000000 : ℝ)|^4397 ≤ (4266703970749/10000000000000 : ℝ)^3373
        have hw : |(1040564019/2000000000 : ℝ)|=(1040564019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s2_1 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83744297/156250000 : ℝ)*x 0 + (-417694927/2000000000 : ℝ)*x 1 + (2601409973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83744297/156250000 : ℝ)^4397 ≤ (2771941884961/6250000000000 : ℝ)^3373 := by
    have hnat : (83744297 : ℕ)^4397*6250000000000^3373 ≤ 2771941884961^3373*156250000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83744297 156250000 2771941884961 6250000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417694927/2000000000 : ℝ)^4397 ≤ (2596378343621/20000000000000 : ℝ)^3373 := by
    have hnat : (417694927 : ℕ)^4397*20000000000000^3373 ≤ 2596378343621^3373*2000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417694927 2000000000 2596378343621 20000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601409973/5000000000 : ℝ)^4397 ≤ (42667038114621/100000000000000 : ℝ)^3373 := by
    have hnat : (2601409973 : ℕ)^4397*100000000000000^3373 ≤ 42667038114621^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601409973 5000000000 42667038114621 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83744297/156250000 : ℝ), (-417694927/2000000000 : ℝ), (2601409973/5000000000 : ℝ)] ![(2771941884961/6250000000000 : ℝ), (2596378343621/20000000000000 : ℝ), (42667038114621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83744297/156250000 : ℝ)|^4397 ≤ (2771941884961/6250000000000 : ℝ)^3373
        have hw : |(83744297/156250000 : ℝ)|=(83744297/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417694927/2000000000 : ℝ)|^4397 ≤ (2596378343621/20000000000000 : ℝ)^3373
        have hw : |(-417694927/2000000000 : ℝ)|=(417694927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601409973/5000000000 : ℝ)|^4397 ≤ (42667038114621/100000000000000 : ℝ)^3373
        have hw : |(2601409973/5000000000 : ℝ)|=(2601409973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s2_2 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071926913/2000000000 : ℝ)*x 0 + (2601410213/5000000000 : ℝ)*x 1 + (-208847459/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071926913/2000000000 : ℝ)^4397 ≤ (44351065380643/100000000000000 : ℝ)^3373 := by
    have hnat : (1071926913 : ℕ)^4397*100000000000000^3373 ≤ 44351065380643^3373*2000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071926913 2000000000 44351065380643 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601410213/5000000000 : ℝ)^4397 ≤ (42667043246011/100000000000000 : ℝ)^3373 := by
    have hnat : (2601410213 : ℕ)^4397*100000000000000^3373 ≤ 42667043246011^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601410213 5000000000 42667043246011 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208847459/1000000000 : ℝ)^4397 ≤ (12981891353467/100000000000000 : ℝ)^3373 := by
    have hnat : (208847459 : ℕ)^4397*100000000000000^3373 ≤ 12981891353467^3373*1000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208847459 1000000000 12981891353467 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071926913/2000000000 : ℝ), (2601410213/5000000000 : ℝ), (-208847459/1000000000 : ℝ)] ![(44351065380643/100000000000000 : ℝ), (42667043246011/100000000000000 : ℝ), (12981891353467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071926913/2000000000 : ℝ)|^4397 ≤ (44351065380643/100000000000000 : ℝ)^3373
        have hw : |(1071926913/2000000000 : ℝ)|=(1071926913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601410213/5000000000 : ℝ)|^4397 ≤ (42667043246011/100000000000000 : ℝ)^3373
        have hw : |(2601410213/5000000000 : ℝ)|=(2601410213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208847459/1000000000 : ℝ)|^4397 ≤ (12981891353467/100000000000000 : ℝ)^3373
        have hw : |(-208847459/1000000000 : ℝ)|=(208847459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s2_3 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298173171/10000000000 : ℝ)*x 0 + (4030960997/10000000000 : ℝ)*x 1 + (71580241/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298173171/10000000000 : ℝ)^4397 ≤ (33262398094543/100000000000000 : ℝ)^3373 := by
    have hnat : (4298173171 : ℕ)^4397*100000000000000^3373 ≤ 33262398094543^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298173171 10000000000 33262398094543 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030960997/10000000000 : ℝ)^4397 ≤ (30592548182993/100000000000000 : ℝ)^3373 := by
    have hnat : (4030960997 : ℕ)^4397*100000000000000^3373 ≤ 30592548182993^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030960997 10000000000 30592548182993 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71580241/156250000 : ℝ)^4397 ≤ (36145053716103/100000000000000 : ℝ)^3373 := by
    have hnat : (71580241 : ℕ)^4397*100000000000000^3373 ≤ 36145053716103^3373*156250000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71580241 156250000 36145053716103 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298173171/10000000000 : ℝ), (4030960997/10000000000 : ℝ), (71580241/156250000 : ℝ)] ![(33262398094543/100000000000000 : ℝ), (30592548182993/100000000000000 : ℝ), (36145053716103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298173171/10000000000 : ℝ)|^4397 ≤ (33262398094543/100000000000000 : ℝ)^3373
        have hw : |(4298173171/10000000000 : ℝ)|=(4298173171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030960997/10000000000 : ℝ)|^4397 ≤ (30592548182993/100000000000000 : ℝ)^3373
        have hw : |(4030960997/10000000000 : ℝ)|=(4030960997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71580241/156250000 : ℝ)|^4397 ≤ (36145053716103/100000000000000 : ℝ)^3373
        have hw : |(71580241/156250000 : ℝ)|=(71580241/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s2_4 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-391620293/2000000000 : ℝ)*x 0 + (1301064843/2500000000 : ℝ)*x 1 + (5454943217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391620293/2000000000 : ℝ)^4397 ≤ (5967814934999/50000000000000 : ℝ)^3373 := by
    have hnat : (391620293 : ℕ)^4397*50000000000000^3373 ≤ 5967814934999^3373*2000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391620293 2000000000 5967814934999 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301064843/2500000000 : ℝ)^4397 ≤ (21341213397927/50000000000000 : ℝ)^3373 := by
    have hnat : (1301064843 : ℕ)^4397*50000000000000^3373 ≤ 21341213397927^3373*2500000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301064843 2500000000 21341213397927 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454943217/10000000000 : ℝ)^4397 ≤ (22690971664317/50000000000000 : ℝ)^3373 := by
    have hnat : (5454943217 : ℕ)^4397*50000000000000^3373 ≤ 22690971664317^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454943217 10000000000 22690971664317 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391620293/2000000000 : ℝ), (1301064843/2500000000 : ℝ), (5454943217/10000000000 : ℝ)] ![(5967814934999/50000000000000 : ℝ), (21341213397927/50000000000000 : ℝ), (22690971664317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391620293/2000000000 : ℝ)|^4397 ≤ (5967814934999/50000000000000 : ℝ)^3373
        have hw : |(-391620293/2000000000 : ℝ)|=(391620293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301064843/2500000000 : ℝ)|^4397 ≤ (21341213397927/50000000000000 : ℝ)^3373
        have hw : |(1301064843/2500000000 : ℝ)|=(1301064843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454943217/10000000000 : ℝ)|^4397 ≤ (22690971664317/50000000000000 : ℝ)^3373
        have hw : |(5454943217/10000000000 : ℝ)|=(5454943217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s2_5 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293647883/10000000000 : ℝ)*x 0 + (-1836350803/10000000000 : ℝ)*x 1 + (5454943921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293647883/10000000000 : ℝ)^4397 ≤ (43640587492999/100000000000000 : ℝ)^3373 := by
    have hnat : (5293647883 : ℕ)^4397*100000000000000^3373 ≤ 43640587492999^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293647883 10000000000 43640587492999 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1836350803/10000000000 : ℝ)^4397 ≤ (10977461534647/100000000000000 : ℝ)^3373 := by
    have hnat : (1836350803 : ℕ)^4397*100000000000000^3373 ≤ 10977461534647^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836350803 10000000000 10977461534647 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454943921/10000000000 : ℝ)^4397 ≤ (1815278038543/4000000000000 : ℝ)^3373 := by
    have hnat : (5454943921 : ℕ)^4397*4000000000000^3373 ≤ 1815278038543^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454943921 10000000000 1815278038543 4000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293647883/10000000000 : ℝ), (-1836350803/10000000000 : ℝ), (5454943921/10000000000 : ℝ)] ![(43640587492999/100000000000000 : ℝ), (10977461534647/100000000000000 : ℝ), (1815278038543/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293647883/10000000000 : ℝ)|^4397 ≤ (43640587492999/100000000000000 : ℝ)^3373
        have hw : |(5293647883/10000000000 : ℝ)|=(5293647883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1836350803/10000000000 : ℝ)|^4397 ≤ (10977461534647/100000000000000 : ℝ)^3373
        have hw : |(-1836350803/10000000000 : ℝ)|=(1836350803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454943921/10000000000 : ℝ)|^4397 ≤ (1815278038543/4000000000000 : ℝ)^3373
        have hw : |(5454943921/10000000000 : ℝ)|=(5454943921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s2_6 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323411893/2500000000 : ℝ)*x 0 + (1090988773/2000000000 : ℝ)*x 1 + (-1836351309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323411893/2500000000 : ℝ)^4397 ≤ (43640584150771/100000000000000 : ℝ)^3373 := by
    have hnat : (1323411893 : ℕ)^4397*100000000000000^3373 ≤ 43640584150771^3373*2500000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323411893 2500000000 43640584150771 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090988773/2000000000 : ℝ)^4397 ≤ (7261112057/16000000000 : ℝ)^3373 := by
    have hnat : (1090988773 : ℕ)^4397*16000000000^3373 ≤ 7261112057^3373*2000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090988773 2000000000 7261112057 16000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1836351309/10000000000 : ℝ)^4397 ≤ (10977465477739/100000000000000 : ℝ)^3373 := by
    have hnat : (1836351309 : ℕ)^4397*100000000000000^3373 ≤ 10977465477739^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836351309 10000000000 10977465477739 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323411893/2500000000 : ℝ), (1090988773/2000000000 : ℝ), (-1836351309/10000000000 : ℝ)] ![(43640584150771/100000000000000 : ℝ), (7261112057/16000000000 : ℝ), (10977465477739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323411893/2500000000 : ℝ)|^4397 ≤ (43640584150771/100000000000000 : ℝ)^3373
        have hw : |(1323411893/2500000000 : ℝ)|=(1323411893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090988773/2000000000 : ℝ)|^4397 ≤ (7261112057/16000000000 : ℝ)^3373
        have hw : |(1090988773/2000000000 : ℝ)|=(1090988773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1836351309/10000000000 : ℝ)|^4397 ≤ (10977465477739/100000000000000 : ℝ)^3373
        have hw : |(-1836351309/10000000000 : ℝ)|=(1836351309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1437_s2_7 (p : ℝ) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298268639/10000000000 : ℝ)*x 0 + (4578013369/10000000000 : ℝ)*x 1 + (2017054323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298268639/10000000000 : ℝ)^4397 ≤ (16631680594697/50000000000000 : ℝ)^3373 := by
    have hnat : (4298268639 : ℕ)^4397*50000000000000^3373 ≤ 16631680594697^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298268639 10000000000 16631680594697 50000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4578013369/10000000000 : ℝ)^4397 ≤ (4514118230891/12500000000000 : ℝ)^3373 := by
    have hnat : (4578013369 : ℕ)^4397*12500000000000^3373 ≤ 4514118230891^3373*10000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578013369 10000000000 4514118230891 12500000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017054323/5000000000 : ℝ)^4397 ≤ (30623692939759/100000000000000 : ℝ)^3373 := by
    have hnat : (2017054323 : ℕ)^4397*100000000000000^3373 ≤ 30623692939759^3373*5000000000^4397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017054323 5000000000 30623692939759 100000000000000 4397 3373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4397/1024 : ℝ)) 4397 3373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298268639/10000000000 : ℝ), (4578013369/10000000000 : ℝ), (2017054323/5000000000 : ℝ)] ![(16631680594697/50000000000000 : ℝ), (4514118230891/12500000000000 : ℝ), (30623692939759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298268639/10000000000 : ℝ)|^4397 ≤ (16631680594697/50000000000000 : ℝ)^3373
        have hw : |(4298268639/10000000000 : ℝ)|=(4298268639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4578013369/10000000000 : ℝ)|^4397 ≤ (4514118230891/12500000000000 : ℝ)^3373
        have hw : |(4578013369/10000000000 : ℝ)|=(4578013369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017054323/5000000000 : ℝ)|^4397 ≤ (30623692939759/100000000000000 : ℝ)^3373
        have hw : |(2017054323/5000000000 : ℝ)|=(2017054323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1437_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7717/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1041/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (631/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7717/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7717/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7717/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7717/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7717/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7717/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7717/100000 : ℝ) ^ (1099/256 : ℝ) ≤ (41859225397137/2500000000000000000 : ℝ) := by
    have hpowers : (7717/100000 : ℝ)^1099 ≤ (41859225397137/2500000000000000000 : ℝ)^256 := by
      have hnat : (7717 : ℕ)^1099*2500000000000000000^256 ≤ 41859225397137^256*100000^1099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7717 100000 41859225397137 2500000000000000000 1099 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7717/100000 : ℝ)) (X := (41859225397137/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hpowhi : (18793/100000 : ℝ) ^ (1099/256 : ℝ) ≤ (38217124604677669/50000000000000000000 : ℝ) := by
    have hpowers : (18793/100000 : ℝ)^1099 ≤ (38217124604677669/50000000000000000000 : ℝ)^256 := by
      have hnat : (18793 : ℕ)^1099*50000000000000000000^256 ≤ 38217124604677669^256*100000^1099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18793 100000 38217124604677669 50000000000000000000 1099 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18793/100000 : ℝ)) (X := (38217124604677669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250041859225397137/1250000000000000000 : ℝ) ≤ (1250009750522361/1250000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (1250041859225397137/1250000000000000000 : ℝ)^256 ≤ (1250009750522361/1250000000000000 : ℝ)^1099 := by
      have hnat : (1250041859225397137 : ℕ)^256*1250000000000000^1099 ≤ 1250009750522361^1099*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250041859225397137 1250000000000000000 1250009750522361 1250000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009750522361/1250000000000000 : ℝ)) (X := (1250041859225397137/1250000000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50039054309112620409/50000000000000000000 : ℝ) ≤ (2000363781963043/2000000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (50039054309112620409/50000000000000000000 : ℝ)^256 ≤ (2000363781963043/2000000000000000 : ℝ)^1099 := by
      have hnat : (50039054309112620409 : ℕ)^256*2000000000000000^1099 ≤ 2000363781963043^1099*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039054309112620409 50000000000000000000 2000363781963043 2000000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000363781963043/2000000000000000 : ℝ)) (X := (50039054309112620409/50000000000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25038217124604677669/25000000000000000000 : ℝ) ≤ (5001779907725771/5000000000000000 : ℝ) ^ (1099/256 : ℝ) := by
    have hpowers : (25038217124604677669/25000000000000000000 : ℝ)^256 ≤ (5001779907725771/5000000000000000 : ℝ)^1099 := by
      have hnat : (25038217124604677669 : ℕ)^256*5000000000000000^1099 ≤ 5001779907725771^1099*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038217124604677669 25000000000000000000 5001779907725771 5000000000000000 256 1099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001779907725771/5000000000000000 : ℝ)) (X := (25038217124604677669/25000000000000000000 : ℝ)) (by norm_num) 1099 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(41859225397137/2500000000000000000 : ℝ) ≤ ((851799960282263789/852000000000000000 : ℝ)+2*(133915818179/85200000000000 : ℝ)*(7717/100000 : ℝ))^(1099/256 : ℝ) := by
    rw [show (851799960282263789/852000000000000000 : ℝ)+2*(133915818179/85200000000000 : ℝ)*(7717/100000 : ℝ)=(1250009750522361/1250000000000000 : ℝ) by norm_num, show 1+2*(41859225397137/2500000000000000000 : ℝ)=(1250041859225397137/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38217124604677669/50000000000000000000 : ℝ)+(41859225397137/2500000000000000000 : ℝ) ≤ ((851799960282263789/852000000000000000 : ℝ)+(133915818179/85200000000000 : ℝ)*((18793/100000 : ℝ)+(7717/100000 : ℝ)))^(1099/256 : ℝ) := by
    rw [show (851799960282263789/852000000000000000 : ℝ)+(133915818179/85200000000000 : ℝ)*((18793/100000 : ℝ)+(7717/100000 : ℝ))=(2000363781963043/2000000000000000 : ℝ) by norm_num, show 1+(38217124604677669/50000000000000000000 : ℝ)+(41859225397137/2500000000000000000 : ℝ)=(50039054309112620409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38217124604677669/50000000000000000000 : ℝ) ≤ ((851799960282263789/852000000000000000 : ℝ)+2*(133915818179/85200000000000 : ℝ)*(18793/100000 : ℝ))^(1099/256 : ℝ) := by
    rw [show (851799960282263789/852000000000000000 : ℝ)+2*(133915818179/85200000000000 : ℝ)*(18793/100000 : ℝ)=(5001779907725771/5000000000000000 : ℝ) by norm_num, show 1+2*(38217124604677669/50000000000000000000 : ℝ)=(25038217124604677669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (851799960282263789/852000000000000000 : ℝ)*(X 1 0+X 2 0)+(133915818179/85200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (7717/100000 : ℝ)) (hi := (18793/100000 : ℝ)) (c := (851799960282263789/852000000000000000 : ℝ)) (alpha := (133915818179/85200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (851799960282263789/852000000000000000 : ℝ)*(X 0 1+X 2 1)+(133915818179/85200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (7717/100000 : ℝ)) (hi := (18793/100000 : ℝ)) (c := (851799960282263789/852000000000000000 : ℝ)) (alpha := (133915818179/85200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (851799960282263789/852000000000000000 : ℝ)*(X 0 2+X 1 2)+(133915818179/85200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1099/256 : ℝ)) (lo := (7717/100000 : ℝ)) (hi := (18793/100000 : ℝ)) (c := (851799960282263789/852000000000000000 : ℝ)) (alpha := (133915818179/85200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-391611499/2000000000 : ℝ)*X 0 0+(5456394181/10000000000 : ℝ)*X 0 1+(1040564019/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83744297/156250000 : ℝ)*X 1 0+(-417694927/2000000000 : ℝ)*X 1 1+(2601409973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071926913/2000000000 : ℝ)*X 2 0+(2601410213/5000000000 : ℝ)*X 2 1+(-208847459/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298173171/10000000000 : ℝ)*X 0 0+(4030960997/10000000000 : ℝ)*X 0 1+(71580241/156250000 : ℝ)*X 0 2+(4298173171/10000000000 : ℝ)*X 1 0+(4030960997/10000000000 : ℝ)*X 1 1+(71580241/156250000 : ℝ)*X 1 2+(4298173171/10000000000 : ℝ)*X 2 0+(4030960997/10000000000 : ℝ)*X 2 1+(71580241/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-391620293/2000000000 : ℝ)*X 0 0+(1301064843/2500000000 : ℝ)*X 0 1+(5454943217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293647883/10000000000 : ℝ)*X 1 0+(-1836350803/10000000000 : ℝ)*X 1 1+(5454943921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323411893/2500000000 : ℝ)*X 2 0+(1090988773/2000000000 : ℝ)*X 2 1+(-1836351309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298268639/10000000000 : ℝ)*X 0 0+(4578013369/10000000000 : ℝ)*X 0 1+(2017054323/5000000000 : ℝ)*X 0 2+(4298268639/10000000000 : ℝ)*X 1 0+(4578013369/10000000000 : ℝ)*X 1 1+(2017054323/5000000000 : ℝ)*X 1 2+(4298268639/10000000000 : ℝ)*X 2 0+(4578013369/10000000000 : ℝ)*X 2 1+(2017054323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1437_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5487872294259221614426503/887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76612331/10000000000000 : ℝ)*(base19) + (53054831/25000000000000 : ℝ)*(base23) + (122169403/100000000000000 : ℝ)*(lower2) + (22002777/10000000000000 : ℝ)*(upper3) + (4232181/25000000000000 : ℝ)*(upper5) + (180038928605109/6250000000000 : ℝ)*(major0) + (180038928605109/6250000000000 : ℝ)*(major1) + (180038928605109/6250000000000 : ℝ)*(major2) + (123238409928129/3125000000000 : ℝ)*(sp0) + (3943631871097297/100000000000000 : ℝ)*(sp1) + (1971816212500641/50000000000000 : ℝ)*(sp2) + (454402036187423/25000000000000 : ℝ)*(sp3) + (3519520479/100000000000000 : ℝ)*(sp4) + (4727275909/100000000000000 : ℝ)*(sp7) + (142001005627/7812500000 : ℝ)*(f.failure) + (3943632637220607/100000000000000 : ℝ)*(f.sum) + (353766313527/88750000000000000000000000 : ℝ)*base65 + (20475580238872333/1775000000000000000000000000000 : ℝ)*base68 + (19996839706472333/1775000000000000000000000000000 : ℝ)*base70 + (29392966986822333/1775000000000000000000000000000 : ℝ)*base72 + (238943285451/177500000000000000000000000 : ℝ)*base74 + (33455196531197333/1775000000000000000000000000000 : ℝ)*base76 + (20164988630172333/1775000000000000000000000000000 : ℝ)*base78 + (25378044641272333/1775000000000000000000000000000 : ℝ)*base80 + (248747639719/177500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (21/15625000000000000 : ℝ)*base90 + (21/15625000000000000 : ℝ)*base92 + (21/15625000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (528644013336480989540751/88750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4966903/5000000000000 : ℝ)*(base19) + (2928701/3125000000000 : ℝ)*(base23) + (172010193/100000000000000 : ℝ)*(upper3) + (33491467/25000000000000 : ℝ)*(lower4) + (18211376232453/625000000000 : ℝ)*(major0) + (18211376232453/625000000000 : ℝ)*(major1) + (18211376232453/625000000000 : ℝ)*(major2) + (3053473573/50000000000000 : ℝ)*(sp1) + (2077506917/50000000000000 : ℝ)*(sp2) + (512274393/50000000000000 : ℝ)*(sp3) + (1994540247890093/50000000000000 : ℝ)*(sp4) + (199453714474749/5000000000000 : ℝ)*(sp5) + (3989076247047921/100000000000000 : ℝ)*(sp6) + (367711735100847/20000000000000 : ℝ)*(sp7) + (919279850026511/50000000000000 : ℝ)*(f.failure) + (1994540247890093/50000000000000 : ℝ)*(f.sum) + (44428051519/71000000000000000000000000 : ℝ)*base66 + (1868504944309361/177500000000000000000000000000 : ℝ)*base68 + (588710221751861/177500000000000000000000000000 : ℝ)*base70 + (1979992788384361/177500000000000000000000000000 : ℝ)*base72 + (31040918407/14200000000000000000000000 : ℝ)*base73 + (1111251111036861/177500000000000000000000000000 : ℝ)*base76 + (1306461142119361/177500000000000000000000000000 : ℝ)*base78 + (3186500088676861/177500000000000000000000000000 : ℝ)*base80 + (466138604057/71000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1306947/100000000000000000000 : ℝ)*base89 + (1306947/100000000000000000000 : ℝ)*base91 + (1306947/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1437_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7717/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1041/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (631/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1437_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1437_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1041/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (631/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1437_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1437_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1437_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1099/256 : ℝ) ≤ p) (hpb : p ≤ (4397/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3169677/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1041/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (631/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1437_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
