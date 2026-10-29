-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:03.577111+00:00
-- url     : https://prove2.me/submissions/9ff2ccb2-0c8d-4998-91bb-21eb732297e3

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
theorem support_rectangle_w1352_s6_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-407071887/2000000000 : ℝ)*x 0 + (1353051063/2500000000 : ℝ)*x 1 + (41959197/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407071887/2000000000 : ℝ)^539 ≤ (12397308217647/100000000000000 : ℝ)^411 := by
    have hnat : (407071887 : ℕ)^539*100000000000000^411 ≤ 12397308217647^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407071887 2000000000 12397308217647 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353051063/2500000000 : ℝ)^539 ≤ (44703077858103/100000000000000 : ℝ)^411 := by
    have hnat : (1353051063 : ℕ)^539*100000000000000^411 ≤ 44703077858103^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353051063 2500000000 44703077858103 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41959197/80000000 : ℝ)^539 ≤ (42899613914837/100000000000000 : ℝ)^411 := by
    have hnat : (41959197 : ℕ)^539*100000000000000^411 ≤ 42899613914837^411*80000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41959197 80000000 42899613914837 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407071887/2000000000 : ℝ), (1353051063/2500000000 : ℝ), (41959197/80000000 : ℝ)] ![(12397308217647/100000000000000 : ℝ), (44703077858103/100000000000000 : ℝ), (42899613914837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407071887/2000000000 : ℝ)|^539 ≤ (12397308217647/100000000000000 : ℝ)^411
        have hw : |(-407071887/2000000000 : ℝ)|=(407071887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353051063/2500000000 : ℝ)|^539 ≤ (44703077858103/100000000000000 : ℝ)^411
        have hw : |(1353051063/2500000000 : ℝ)|=(1353051063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41959197/80000000 : ℝ)|^539 ≤ (42899613914837/100000000000000 : ℝ)^411
        have hw : |(41959197/80000000 : ℝ)|=(41959197/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s6_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348827059/10000000000 : ℝ)*x 0 + (-2120594641/10000000000 : ℝ)*x 1 + (655612451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348827059/10000000000 : ℝ)^539 ≤ (22008914433013/50000000000000 : ℝ)^411 := by
    have hnat : (5348827059 : ℕ)^539*50000000000000^411 ≤ 22008914433013^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348827059 10000000000 22008914433013 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120594641/10000000000 : ℝ)^539 ≤ (261651147717/2000000000000 : ℝ)^411 := by
    have hnat : (2120594641 : ℕ)^539*2000000000000^411 ≤ 261651147717^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120594641 10000000000 261651147717 2000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655612451/1250000000 : ℝ)^539 ≤ (10724903433121/25000000000000 : ℝ)^411 := by
    have hnat : (655612451 : ℕ)^539*25000000000000^411 ≤ 10724903433121^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655612451 1250000000 10724903433121 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348827059/10000000000 : ℝ), (-2120594641/10000000000 : ℝ), (655612451/1250000000 : ℝ)] ![(22008914433013/50000000000000 : ℝ), (261651147717/2000000000000 : ℝ), (10724903433121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348827059/10000000000 : ℝ)|^539 ≤ (22008914433013/50000000000000 : ℝ)^411
        have hw : |(5348827059/10000000000 : ℝ)|=(5348827059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2120594641/10000000000 : ℝ)|^539 ≤ (261651147717/2000000000000 : ℝ)^411
        have hw : |(-2120594641/10000000000 : ℝ)|=(2120594641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655612451/1250000000 : ℝ)|^539 ≤ (10724903433121/25000000000000 : ℝ)^411
        have hw : |(655612451/1250000000 : ℝ)|=(655612451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s6_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668603377/1250000000 : ℝ)*x 0 + (41959197/80000000 : ℝ)*x 1 + (-84823787/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668603377/1250000000 : ℝ)^539 ≤ (44017828401953/100000000000000 : ℝ)^411 := by
    have hnat : (668603377 : ℕ)^539*100000000000000^411 ≤ 44017828401953^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668603377 1250000000 44017828401953 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41959197/80000000 : ℝ)^539 ≤ (42899613914837/100000000000000 : ℝ)^411 := by
    have hnat : (41959197 : ℕ)^539*100000000000000^411 ≤ 42899613914837^411*80000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41959197 80000000 42899613914837 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84823787/400000000 : ℝ)^539 ≤ (13082557660931/100000000000000 : ℝ)^411 := by
    have hnat : (84823787 : ℕ)^539*100000000000000^411 ≤ 13082557660931^411*400000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84823787 400000000 13082557660931 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668603377/1250000000 : ℝ), (41959197/80000000 : ℝ), (-84823787/400000000 : ℝ)] ![(44017828401953/100000000000000 : ℝ), (42899613914837/100000000000000 : ℝ), (13082557660931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668603377/1250000000 : ℝ)|^539 ≤ (44017828401953/100000000000000 : ℝ)^411
        have hw : |(668603377/1250000000 : ℝ)|=(668603377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41959197/80000000 : ℝ)|^539 ≤ (42899613914837/100000000000000 : ℝ)^411
        have hw : |(41959197/80000000 : ℝ)|=(41959197/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84823787/400000000 : ℝ)|^539 ≤ (13082557660931/100000000000000 : ℝ)^411
        have hw : |(-84823787/400000000 : ℝ)|=(84823787/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s6_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (270250621/625000000 : ℝ)*x 0 + (4151462669/10000000000 : ℝ)*x 1 + (4503213303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270250621/625000000 : ℝ)^539 ≤ (16651711055179/50000000000000 : ℝ)^411 := by
    have hnat : (270250621 : ℕ)^539*50000000000000^411 ≤ 16651711055179^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270250621 625000000 16651711055179 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4151462669/10000000000 : ℝ)^539 ≤ (31571513967041/100000000000000 : ℝ)^411 := by
    have hnat : (4151462669 : ℕ)^539*100000000000000^411 ≤ 31571513967041^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151462669 10000000000 31571513967041 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503213303/10000000000 : ℝ)^539 ≤ (35125063896457/100000000000000 : ℝ)^411 := by
    have hnat : (4503213303 : ℕ)^539*100000000000000^411 ≤ 35125063896457^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503213303 10000000000 35125063896457 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270250621/625000000 : ℝ), (4151462669/10000000000 : ℝ), (4503213303/10000000000 : ℝ)] ![(16651711055179/50000000000000 : ℝ), (31571513967041/100000000000000 : ℝ), (35125063896457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270250621/625000000 : ℝ)|^539 ≤ (16651711055179/50000000000000 : ℝ)^411
        have hw : |(270250621/625000000 : ℝ)|=(270250621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4151462669/10000000000 : ℝ)|^539 ≤ (31571513967041/100000000000000 : ℝ)^411
        have hw : |(4151462669/10000000000 : ℝ)|=(4151462669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503213303/10000000000 : ℝ)|^539 ≤ (35125063896457/100000000000000 : ℝ)^411
        have hw : |(4503213303/10000000000 : ℝ)|=(4503213303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s6_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2035371561/10000000000 : ℝ)*x 0 + (5245498849/10000000000 : ℝ)*x 1 + (676450237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035371561/10000000000 : ℝ)^539 ≤ (3099351269787/25000000000000 : ℝ)^411 := by
    have hnat : (2035371561 : ℕ)^539*25000000000000^411 ≤ 3099351269787^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035371561 10000000000 3099351269787 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245498849/10000000000 : ℝ)^539 ≤ (4290604168103/10000000000000 : ℝ)^411 := by
    have hnat : (5245498849 : ℕ)^539*10000000000000^411 ≤ 4290604168103^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245498849 10000000000 4290604168103 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676450237/1250000000 : ℝ)^539 ≤ (44696553227861/100000000000000 : ℝ)^411 := by
    have hnat : (676450237 : ℕ)^539*100000000000000^411 ≤ 44696553227861^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676450237 1250000000 44696553227861 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2035371561/10000000000 : ℝ), (5245498849/10000000000 : ℝ), (676450237/1250000000 : ℝ)] ![(3099351269787/25000000000000 : ℝ), (4290604168103/10000000000000 : ℝ), (44696553227861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2035371561/10000000000 : ℝ)|^539 ≤ (3099351269787/25000000000000 : ℝ)^411
        have hw : |(-2035371561/10000000000 : ℝ)|=(2035371561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245498849/10000000000 : ℝ)|^539 ≤ (4290604168103/10000000000000 : ℝ)^411
        have hw : |(5245498849/10000000000 : ℝ)|=(5245498849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676450237/1250000000 : ℝ)|^539 ≤ (44696553227861/100000000000000 : ℝ)^411
        have hw : |(676450237/1250000000 : ℝ)|=(676450237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s6_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305684569/10000000000 : ℝ)*x 0 + (-976946233/5000000000 : ℝ)*x 1 + (5411601041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305684569/10000000000 : ℝ)^539 ≤ (43552804845609/100000000000000 : ℝ)^411 := by
    have hnat : (5305684569 : ℕ)^539*100000000000000^411 ≤ 43552804845609^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305684569 10000000000 43552804845609 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976946233/5000000000 : ℝ)^539 ≤ (1468831395899/12500000000000 : ℝ)^411 := by
    have hnat : (976946233 : ℕ)^539*12500000000000^411 ≤ 1468831395899^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976946233 5000000000 1468831395899 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411601041/10000000000 : ℝ)^539 ≤ (4469654396679/10000000000000 : ℝ)^411 := by
    have hnat : (5411601041 : ℕ)^539*10000000000000^411 ≤ 4469654396679^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411601041 10000000000 4469654396679 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305684569/10000000000 : ℝ), (-976946233/5000000000 : ℝ), (5411601041/10000000000 : ℝ)] ![(43552804845609/100000000000000 : ℝ), (1468831395899/12500000000000 : ℝ), (4469654396679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305684569/10000000000 : ℝ)|^539 ≤ (43552804845609/100000000000000 : ℝ)^411
        have hw : |(5305684569/10000000000 : ℝ)|=(5305684569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976946233/5000000000 : ℝ)|^539 ≤ (1468831395899/12500000000000 : ℝ)^411
        have hw : |(-976946233/5000000000 : ℝ)|=(976946233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411601041/10000000000 : ℝ)|^539 ≤ (4469654396679/10000000000000 : ℝ)^411
        have hw : |(5411601041/10000000000 : ℝ)|=(5411601041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s6_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (82901323/156250000 : ℝ)*x 0 + (2705800447/5000000000 : ℝ)*x 1 + (-122118283/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82901323/156250000 : ℝ)^539 ≤ (43552805954423/100000000000000 : ℝ)^411 := by
    have hnat : (82901323 : ℕ)^539*100000000000000^411 ≤ 43552805954423^411*156250000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82901323 156250000 43552805954423 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705800447/5000000000 : ℝ)^539 ≤ (8939308474907/20000000000000 : ℝ)^411 := by
    have hnat : (2705800447 : ℕ)^539*20000000000000^411 ≤ 8939308474907^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705800447 5000000000 8939308474907 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122118283/625000000 : ℝ)^539 ≤ (5875325828091/50000000000000 : ℝ)^411 := by
    have hnat : (122118283 : ℕ)^539*50000000000000^411 ≤ 5875325828091^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122118283 625000000 5875325828091 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82901323/156250000 : ℝ), (2705800447/5000000000 : ℝ), (-122118283/625000000 : ℝ)] ![(43552805954423/100000000000000 : ℝ), (8939308474907/20000000000000 : ℝ), (5875325828091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82901323/156250000 : ℝ)|^539 ≤ (43552805954423/100000000000000 : ℝ)^411
        have hw : |(82901323/156250000 : ℝ)|=(82901323/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705800447/5000000000 : ℝ)|^539 ≤ (8939308474907/20000000000000 : ℝ)^411
        have hw : |(2705800447/5000000000 : ℝ)|=(2705800447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122118283/625000000 : ℝ)|^539 ≤ (5875325828091/50000000000000 : ℝ)^411
        have hw : |(-122118283/625000000 : ℝ)|=(122118283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s6_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4324035163/10000000000 : ℝ)*x 0 + (900390589/2000000000 : ℝ)*x 1 + (830545939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324035163/10000000000 : ℝ)^539 ≤ (33303676919569/100000000000000 : ℝ)^411 := by
    have hnat : (4324035163 : ℕ)^539*100000000000000^411 ≤ 33303676919569^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324035163 10000000000 33303676919569 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900390589/2000000000 : ℝ)^539 ≤ (35112172007953/100000000000000 : ℝ)^411 := by
    have hnat : (900390589 : ℕ)^539*100000000000000^411 ≤ 35112172007953^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900390589 2000000000 35112172007953 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830545939/2000000000 : ℝ)^539 ≤ (157920755329/500000000000 : ℝ)^411 := by
    have hnat : (830545939 : ℕ)^539*500000000000^411 ≤ 157920755329^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830545939 2000000000 157920755329 500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324035163/10000000000 : ℝ), (900390589/2000000000 : ℝ), (830545939/2000000000 : ℝ)] ![(33303676919569/100000000000000 : ℝ), (35112172007953/100000000000000 : ℝ), (157920755329/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324035163/10000000000 : ℝ)|^539 ≤ (33303676919569/100000000000000 : ℝ)^411
        have hw : |(4324035163/10000000000 : ℝ)|=(4324035163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900390589/2000000000 : ℝ)|^539 ≤ (35112172007953/100000000000000 : ℝ)^411
        have hw : |(900390589/2000000000 : ℝ)|=(900390589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830545939/2000000000 : ℝ)|^539 ≤ (157920755329/500000000000 : ℝ)^411
        have hw : |(830545939/2000000000 : ℝ)|=(830545939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7357/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2233/20000 : ℝ) ^ (4311/1024 : ℝ) ≤ (9806689738101827/100000000000000000000 : ℝ) := by
    have hpowers : (2233/20000 : ℝ)^4311 ≤ (9806689738101827/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2233 : ℕ)^4311*100000000000000000000^1024 ≤ 9806689738101827^1024*20000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2233 20000 9806689738101827 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2233/20000 : ℝ)) (X := (9806689738101827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14721/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (31408600740173063/100000000000000000000 : ℝ) := by
    have hpowers : (14721/100000 : ℝ)^4311 ≤ (31408600740173063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14721 : ℕ)^4311*100000000000000000000^1024 ≤ 31408600740173063^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14721 100000 31408600740173063 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14721/100000 : ℝ)) (X := (31408600740173063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009806689738101827/50000000000000000000 : ℝ) ≤ (2500116461372133/2500000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50009806689738101827/50000000000000000000 : ℝ)^1024 ≤ (2500116461372133/2500000000000000 : ℝ)^4311 := by
      have hnat : (50009806689738101827 : ℕ)^1024*2500000000000000^4311 ≤ 2500116461372133^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009806689738101827 50000000000000000000 2500116461372133 2500000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500116461372133/2500000000000000 : ℝ)) (X := (50009806689738101827/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004121529047827489/10000000000000000000 : ℝ) ≤ (5000489420408339/5000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (10004121529047827489/10000000000000000000 : ℝ)^1024 ≤ (5000489420408339/5000000000000000 : ℝ)^4311 := by
      have hnat : (10004121529047827489 : ℕ)^1024*5000000000000000^4311 ≤ 5000489420408339^4311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004121529047827489 10000000000000000000 5000489420408339 5000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000489420408339/5000000000000000 : ℝ)) (X := (10004121529047827489/10000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031408600740173063/50000000000000000000 : ℝ) ≤ (1250186479518103/1250000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50031408600740173063/50000000000000000000 : ℝ)^1024 ≤ (1250186479518103/1250000000000000 : ℝ)^4311 := by
      have hnat : (50031408600740173063 : ℕ)^1024*1250000000000000^4311 ≤ 1250186479518103^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031408600740173063 50000000000000000000 1250186479518103 1250000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250186479518103/1250000000000000 : ℝ)) (X := (50031408600740173063/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9806689738101827/100000000000000000000 : ℝ) ≤ ((1269650048602847129/1270000000000000000 : ℝ)+2*(36642523439/25400000000000 : ℝ)*(2233/20000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (1269650048602847129/1270000000000000000 : ℝ)+2*(36642523439/25400000000000 : ℝ)*(2233/20000 : ℝ)=(2500116461372133/2500000000000000 : ℝ) by norm_num, show 1+2*(9806689738101827/100000000000000000000 : ℝ)=(50009806689738101827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31408600740173063/100000000000000000000 : ℝ)+(9806689738101827/100000000000000000000 : ℝ) ≤ ((1269650048602847129/1270000000000000000 : ℝ)+(36642523439/25400000000000 : ℝ)*((14721/100000 : ℝ)+(2233/20000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (1269650048602847129/1270000000000000000 : ℝ)+(36642523439/25400000000000 : ℝ)*((14721/100000 : ℝ)+(2233/20000 : ℝ))=(5000489420408339/5000000000000000 : ℝ) by norm_num, show 1+(31408600740173063/100000000000000000000 : ℝ)+(9806689738101827/100000000000000000000 : ℝ)=(10004121529047827489/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31408600740173063/100000000000000000000 : ℝ) ≤ ((1269650048602847129/1270000000000000000 : ℝ)+2*(36642523439/25400000000000 : ℝ)*(14721/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (1269650048602847129/1270000000000000000 : ℝ)+2*(36642523439/25400000000000 : ℝ)*(14721/100000 : ℝ)=(1250186479518103/1250000000000000 : ℝ) by norm_num, show 1+2*(31408600740173063/100000000000000000000 : ℝ)=(50031408600740173063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1269650048602847129/1270000000000000000 : ℝ)*(X 1 0+X 2 0)+(36642523439/25400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (1269650048602847129/1270000000000000000 : ℝ)) (alpha := (36642523439/25400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1269650048602847129/1270000000000000000 : ℝ)*(X 0 1+X 2 1)+(36642523439/25400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (1269650048602847129/1270000000000000000 : ℝ)) (alpha := (36642523439/25400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1269650048602847129/1270000000000000000 : ℝ)*(X 0 2+X 1 2)+(36642523439/25400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2233/20000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (1269650048602847129/1270000000000000000 : ℝ)) (alpha := (36642523439/25400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-407071887/2000000000 : ℝ)*X 0 0+(1353051063/2500000000 : ℝ)*X 0 1+(41959197/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348827059/10000000000 : ℝ)*X 1 0+(-2120594641/10000000000 : ℝ)*X 1 1+(655612451/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668603377/1250000000 : ℝ)*X 2 0+(41959197/80000000 : ℝ)*X 2 1+(-84823787/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270250621/625000000 : ℝ)*X 0 0+(4151462669/10000000000 : ℝ)*X 0 1+(4503213303/10000000000 : ℝ)*X 0 2+(270250621/625000000 : ℝ)*X 1 0+(4151462669/10000000000 : ℝ)*X 1 1+(4503213303/10000000000 : ℝ)*X 1 2+(270250621/625000000 : ℝ)*X 2 0+(4151462669/10000000000 : ℝ)*X 2 1+(4503213303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2035371561/10000000000 : ℝ)*X 0 0+(5245498849/10000000000 : ℝ)*X 0 1+(676450237/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305684569/10000000000 : ℝ)*X 1 0+(-976946233/5000000000 : ℝ)*X 1 1+(5411601041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82901323/156250000 : ℝ)*X 2 0+(2705800447/5000000000 : ℝ)*X 2 1+(-122118283/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324035163/10000000000 : ℝ)*X 0 0+(900390589/2000000000 : ℝ)*X 0 1+(830545939/2000000000 : ℝ)*X 0 2+(4324035163/10000000000 : ℝ)*X 1 0+(900390589/2000000000 : ℝ)*X 1 1+(830545939/2000000000 : ℝ)*X 1 2+(4324035163/10000000000 : ℝ)*X 2 0+(900390589/2000000000 : ℝ)*X 2 1+(830545939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174008625092248861229405937/31750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (507983727/50000000000000 : ℝ)*(base19) + (441769697/50000000000000 : ℝ)*(base23) + (22565841/50000000000000 : ℝ)*(lower2) + (29776881/20000000000000 : ℝ)*(upper3) + (9026669/25000000000000 : ℝ)*(upper5) + (2205026800116783/50000000000000 : ℝ)*(major0) + (2205026800116783/50000000000000 : ℝ)*(major1) + (2205026800116783/50000000000000 : ℝ)*(major2) + (5977143887378877/100000000000000 : ℝ)*(sp0) + (747145288835891/12500000000000 : ℝ)*(sp1) + (1494290610778797/25000000000000 : ℝ)*(sp2) + (2842932436060059/100000000000000 : ℝ)*(sp3) + (3887855141/20000000000000 : ℝ)*(sp4) + (562753313/5000000000000 : ℝ)*(sp7) + (35536796139079/1250000000000 : ℝ)*(f.failure) + (2988581663327291/50000000000000 : ℝ)*(f.sum) + (934017983197/635000000000000000000000000 : ℝ)*base65 + (1141282803113116007/63500000000000000000000000000000 : ℝ)*base67 + (703761982576116007/63500000000000000000000000000000 : ℝ)*base69 + (394686541927116007/63500000000000000000000000000000 : ℝ)*base71 + (95612659829/79375000000000000000000000 : ℝ)*base73 + (347978593369616007/63500000000000000000000000000000 : ℝ)*base75 + (1306233965971116007/63500000000000000000000000000000 : ℝ)*base77 + (495649350224616007/63500000000000000000000000000000 : ℝ)*base79 + (1050375919079/317500000000000000000000000 : ℝ)*base82 + (1149489/125000000000000000000 : ℝ)*base89 + (1149489/125000000000000000000 : ℝ)*base91 + (1149489/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5837433888958401342109137/1270000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2548053757/100000000000000 : ℝ)*(base19) + (675016443/25000000000000 : ℝ)*(base23) + (1494901/4000000000000 : ℝ)*(upper2) + (26468651/20000000000000 : ℝ)*(upper5) + (177677386758251/4000000000000 : ℝ)*(major0) + (177677386758251/4000000000000 : ℝ)*(major1) + (177677386758251/4000000000000 : ℝ)*(major2) + (941307509/20000000000000 : ℝ)*(sp0) + (8792556091/20000000000000 : ℝ)*(sp1) + (39621588417/100000000000000 : ℝ)*(sp2) + (6020368637014433/100000000000000 : ℝ)*(sp4) + (1204065366543553/20000000000000 : ℝ)*(sp5) + (1505082755474447/25000000000000 : ℝ)*(sp6) + (2863495841147079/100000000000000 : ℝ)*(sp7) + (2863495841147079/100000000000000 : ℝ)*(f.failure) + (6020373343551977/100000000000000 : ℝ)*(f.sum) + (259528706139/254000000000000000000000000 : ℝ)*base65 + (78466881697098621/5080000000000000000000000000000 : ℝ)*base68 + (66209704717978621/5080000000000000000000000000000 : ℝ)*base70 + (16234404663698621/5080000000000000000000000000000 : ℝ)*base72 + (40054831681/50800000000000000000000000 : ℝ)*base73 + (8966585330938621/5080000000000000000000000000000 : ℝ)*base76 + (42404426379938621/5080000000000000000000000000000 : ℝ)*base78 + (7890389631701379/5080000000000000000000000000000 : ℝ)*base79 + (573855870981/254000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (35977489/10000000000000000000000 : ℝ)*base89 + (35977489/10000000000000000000000 : ℝ)*base91 + (35977489/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1352_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1352_s7_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-127210309/625000000 : ℝ)*x 0 + (1353036843/2500000000 : ℝ)*x 1 + (5244952961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127210309/625000000 : ℝ)^539 ≤ (3099338055767/25000000000000 : ℝ)^411 := by
    have hnat : (127210309 : ℕ)^539*25000000000000^411 ≤ 3099338055767^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127210309 625000000 3099338055767 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353036843/2500000000 : ℝ)^539 ≤ (44702461732767/100000000000000 : ℝ)^411 := by
    have hnat : (1353036843 : ℕ)^539*100000000000000^411 ≤ 44702461732767^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353036843 2500000000 44702461732767 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244952961/10000000000 : ℝ)^539 ≤ (42900186031077/100000000000000 : ℝ)^411 := by
    have hnat : (5244952961 : ℕ)^539*100000000000000^411 ≤ 42900186031077^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244952961 10000000000 42900186031077 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127210309/625000000 : ℝ), (1353036843/2500000000 : ℝ), (5244952961/10000000000 : ℝ)] ![(3099338055767/25000000000000 : ℝ), (44702461732767/100000000000000 : ℝ), (42900186031077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127210309/625000000 : ℝ)|^539 ≤ (3099338055767/25000000000000 : ℝ)^411
        have hw : |(-127210309/625000000 : ℝ)|=(127210309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353036843/2500000000 : ℝ)|^539 ≤ (44702461732767/100000000000000 : ℝ)^411
        have hw : |(1353036843/2500000000 : ℝ)|=(1353036843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244952961/10000000000 : ℝ)|^539 ≤ (42900186031077/100000000000000 : ℝ)^411
        have hw : |(5244952961/10000000000 : ℝ)|=(5244952961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s7_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1337203201/2500000000 : ℝ)*x 0 + (-8283371/39062500 : ℝ)*x 1 + (5244952919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337203201/2500000000 : ℝ)^539 ≤ (5502209377599/12500000000000 : ℝ)^411 := by
    have hnat : (1337203201 : ℕ)^539*12500000000000^411 ≤ 5502209377599^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337203201 2500000000 5502209377599 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8283371/39062500 : ℝ)^539 ≤ (1308213938543/10000000000000 : ℝ)^411 := by
    have hnat : (8283371 : ℕ)^539*10000000000000^411 ≤ 1308213938543^411*39062500^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8283371 39062500 1308213938543 10000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244952919/10000000000 : ℝ)^539 ≤ (42900185580557/100000000000000 : ℝ)^411 := by
    have hnat : (5244952919 : ℕ)^539*100000000000000^411 ≤ 42900185580557^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244952919 10000000000 42900185580557 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337203201/2500000000 : ℝ), (-8283371/39062500 : ℝ), (5244952919/10000000000 : ℝ)] ![(5502209377599/12500000000000 : ℝ), (1308213938543/10000000000000 : ℝ), (42900185580557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337203201/2500000000 : ℝ)|^539 ≤ (5502209377599/12500000000000 : ℝ)^411
        have hw : |(1337203201/2500000000 : ℝ)|=(1337203201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8283371/39062500 : ℝ)|^539 ≤ (1308213938543/10000000000000 : ℝ)^411
        have hw : |(-8283371/39062500 : ℝ)|=(8283371/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244952919/10000000000 : ℝ)|^539 ≤ (42900185580557/100000000000000 : ℝ)^411
        have hw : |(5244952919/10000000000 : ℝ)|=(5244952919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s7_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348812763/10000000000 : ℝ)*x 0 + (5244952991/10000000000 : ℝ)*x 1 + (-424108587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348812763/10000000000 : ℝ)^539 ≤ (8803534915661/20000000000000 : ℝ)^411 := by
    have hnat : (5348812763 : ℕ)^539*20000000000000^411 ≤ 8803534915661^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348812763 10000000000 8803534915661 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244952991/10000000000 : ℝ)^539 ≤ (42900186352877/100000000000000 : ℝ)^411 := by
    have hnat : (5244952991 : ℕ)^539*100000000000000^411 ≤ 42900186352877^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244952991 10000000000 42900186352877 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424108587/2000000000 : ℝ)^539 ≤ (13082139053717/100000000000000 : ℝ)^411 := by
    have hnat : (424108587 : ℕ)^539*100000000000000^411 ≤ 13082139053717^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424108587 2000000000 13082139053717 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348812763/10000000000 : ℝ), (5244952991/10000000000 : ℝ), (-424108587/2000000000 : ℝ)] ![(8803534915661/20000000000000 : ℝ), (42900186352877/100000000000000 : ℝ), (13082139053717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348812763/10000000000 : ℝ)|^539 ≤ (8803534915661/20000000000000 : ℝ)^411
        have hw : |(5348812763/10000000000 : ℝ)|=(5348812763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244952991/10000000000 : ℝ)|^539 ≤ (42900186352877/100000000000000 : ℝ)^411
        have hw : |(5244952991/10000000000 : ℝ)|=(5244952991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424108587/2000000000 : ℝ)|^539 ≤ (13082139053717/100000000000000 : ℝ)^411
        have hw : |(-424108587/2000000000 : ℝ)|=(424108587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s7_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2162006889/5000000000 : ℝ)*x 0 + (2075789149/5000000000 : ℝ)*x 1 + (4503096773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162006889/5000000000 : ℝ)^539 ≤ (33303460917043/100000000000000 : ℝ)^411 := by
    have hnat : (2162006889 : ℕ)^539*100000000000000^411 ≤ 33303460917043^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162006889 5000000000 33303460917043 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075789149/5000000000 : ℝ)^539 ≤ (1578633359047/5000000000000 : ℝ)^411 := by
    have hnat : (2075789149 : ℕ)^539*5000000000000^411 ≤ 1578633359047^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075789149 5000000000 1578633359047 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503096773/10000000000 : ℝ)^539 ≤ (878096797323/2500000000000 : ℝ)^411 := by
    have hnat : (4503096773 : ℕ)^539*2500000000000^411 ≤ 878096797323^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503096773 10000000000 878096797323 2500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162006889/5000000000 : ℝ), (2075789149/5000000000 : ℝ), (4503096773/10000000000 : ℝ)] ![(33303460917043/100000000000000 : ℝ), (1578633359047/5000000000000 : ℝ), (878096797323/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162006889/5000000000 : ℝ)|^539 ≤ (33303460917043/100000000000000 : ℝ)^411
        have hw : |(2162006889/5000000000 : ℝ)|=(2162006889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075789149/5000000000 : ℝ)|^539 ≤ (1578633359047/5000000000000 : ℝ)^411
        have hw : |(2075789149/5000000000 : ℝ)|=(2075789149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503096773/10000000000 : ℝ)|^539 ≤ (878096797323/2500000000000 : ℝ)^411
        have hw : |(4503096773/10000000000 : ℝ)|=(4503096773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s7_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2035377013/10000000000 : ℝ)*x 0 + (5245551731/10000000000 : ℝ)*x 1 + (169110797/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035377013/10000000000 : ℝ)^539 ≤ (12397448629339/100000000000000 : ℝ)^411 := by
    have hnat : (2035377013 : ℕ)^539*100000000000000^411 ≤ 12397448629339^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035377013 10000000000 12397448629339 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245551731/10000000000 : ℝ)^539 ≤ (42906608947549/100000000000000 : ℝ)^411 := by
    have hnat : (5245551731 : ℕ)^539*100000000000000^411 ≤ 42906608947549^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245551731 10000000000 42906608947549 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169110797/312500000 : ℝ)^539 ≤ (11173985602429/25000000000000 : ℝ)^411 := by
    have hnat : (169110797 : ℕ)^539*25000000000000^411 ≤ 11173985602429^411*312500000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169110797 312500000 11173985602429 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2035377013/10000000000 : ℝ), (5245551731/10000000000 : ℝ), (169110797/312500000 : ℝ)] ![(12397448629339/100000000000000 : ℝ), (42906608947549/100000000000000 : ℝ), (11173985602429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2035377013/10000000000 : ℝ)|^539 ≤ (12397448629339/100000000000000 : ℝ)^411
        have hw : |(-2035377013/10000000000 : ℝ)|=(2035377013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245551731/10000000000 : ℝ)|^539 ≤ (42906608947549/100000000000000 : ℝ)^411
        have hw : |(5245551731/10000000000 : ℝ)|=(5245551731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169110797/312500000 : ℝ)|^539 ≤ (11173985602429/25000000000000 : ℝ)^411
        have hw : |(169110797/312500000 : ℝ)|=(169110797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s7_5 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652848999/5000000000 : ℝ)*x 0 + (-7632619/39062500 : ℝ)*x 1 + (676443183/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652848999/5000000000 : ℝ)^539 ≤ (5444118676423/12500000000000 : ℝ)^411 := by
    have hnat : (2652848999 : ℕ)^539*12500000000000^411 ≤ 5444118676423^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652848999 5000000000 5444118676423 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7632619/39062500 : ℝ)^539 ≤ (11751108595717/100000000000000 : ℝ)^411 := by
    have hnat : (7632619 : ℕ)^539*100000000000000^411 ≤ 11751108595717^411*39062500^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7632619 39062500 11751108595717 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676443183/1250000000 : ℝ)^539 ≤ (44695941976451/100000000000000 : ℝ)^411 := by
    have hnat : (676443183 : ℕ)^539*100000000000000^411 ≤ 44695941976451^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676443183 1250000000 44695941976451 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652848999/5000000000 : ℝ), (-7632619/39062500 : ℝ), (676443183/1250000000 : ℝ)] ![(5444118676423/12500000000000 : ℝ), (11751108595717/100000000000000 : ℝ), (44695941976451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652848999/5000000000 : ℝ)|^539 ≤ (5444118676423/12500000000000 : ℝ)^411
        have hw : |(2652848999/5000000000 : ℝ)|=(2652848999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7632619/39062500 : ℝ)|^539 ≤ (11751108595717/100000000000000 : ℝ)^411
        have hw : |(-7632619/39062500 : ℝ)|=(7632619/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676443183/1250000000 : ℝ)|^539 ≤ (44695941976451/100000000000000 : ℝ)^411
        have hw : |(676443183/1250000000 : ℝ)|=(676443183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s7_6 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1061139599/2000000000 : ℝ)*x 0 + (5411545453/10000000000 : ℝ)*x 1 + (-488487621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061139599/2000000000 : ℝ)^539 ≤ (43552949379089/100000000000000 : ℝ)^411 := by
    have hnat : (1061139599 : ℕ)^539*100000000000000^411 ≤ 43552949379089^411*2000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061139599 2000000000 43552949379089 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411545453/10000000000 : ℝ)^539 ≤ (44695941857303/100000000000000 : ℝ)^411 := by
    have hnat : (5411545453 : ℕ)^539*100000000000000^411 ≤ 44695941857303^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411545453 10000000000 44695941857303 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488487621/2500000000 : ℝ)^539 ≤ (5875554376729/50000000000000 : ℝ)^411 := by
    have hnat : (488487621 : ℕ)^539*50000000000000^411 ≤ 5875554376729^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488487621 2500000000 5875554376729 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061139599/2000000000 : ℝ), (5411545453/10000000000 : ℝ), (-488487621/2500000000 : ℝ)] ![(43552949379089/100000000000000 : ℝ), (44695941857303/100000000000000 : ℝ), (5875554376729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061139599/2000000000 : ℝ)|^539 ≤ (43552949379089/100000000000000 : ℝ)^411
        have hw : |(1061139599/2000000000 : ℝ)|=(1061139599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411545453/10000000000 : ℝ)|^539 ≤ (44695941857303/100000000000000 : ℝ)^411
        have hw : |(5411545453/10000000000 : ℝ)|=(5411545453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488487621/2500000000 : ℝ)|^539 ≤ (5875554376729/50000000000000 : ℝ)^411
        have hw : |(-488487621/2500000000 : ℝ)|=(488487621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s7_7 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4324039271/10000000000 : ℝ)*x 0 + (2250918963/5000000000 : ℝ)*x 1 + (4152843481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324039271/10000000000 : ℝ)^539 ≤ (16651859206551/50000000000000 : ℝ)^411 := by
    have hnat : (4324039271 : ℕ)^539*50000000000000^411 ≤ 16651859206551^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324039271 10000000000 16651859206551 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250918963/5000000000 : ℝ)^539 ≤ (35110995563173/100000000000000 : ℝ)^411 := by
    have hnat : (2250918963 : ℕ)^539*100000000000000^411 ≤ 35110995563173^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250918963 5000000000 35110995563173 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152843481/10000000000 : ℝ)^539 ≤ (31585286006503/100000000000000 : ℝ)^411 := by
    have hnat : (4152843481 : ℕ)^539*100000000000000^411 ≤ 31585286006503^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152843481 10000000000 31585286006503 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324039271/10000000000 : ℝ), (2250918963/5000000000 : ℝ), (4152843481/10000000000 : ℝ)] ![(16651859206551/50000000000000 : ℝ), (35110995563173/100000000000000 : ℝ), (31585286006503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324039271/10000000000 : ℝ)|^539 ≤ (16651859206551/50000000000000 : ℝ)^411
        have hw : |(4324039271/10000000000 : ℝ)|=(4324039271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250918963/5000000000 : ℝ)|^539 ≤ (35110995563173/100000000000000 : ℝ)^411
        have hw : |(2250918963/5000000000 : ℝ)|=(2250918963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152843481/10000000000 : ℝ)|^539 ≤ (31585286006503/100000000000000 : ℝ)^411
        have hw : |(4152843481/10000000000 : ℝ)|=(4152843481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11173/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14713/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2793/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2793/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2793/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2793/25000 : ℝ) ^ (4311/1024 : ℝ) ≤ (1966520059725023/20000000000000000000 : ℝ) := by
    have hpowers : (2793/25000 : ℝ)^4311 ≤ (1966520059725023/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2793 : ℕ)^4311*20000000000000000000^1024 ≤ 1966520059725023^1024*25000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2793 25000 1966520059725023 20000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2793/25000 : ℝ)) (X := (1966520059725023/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7357/50000 : ℝ) ^ (4311/1024 : ℝ) ≤ (31345772351093487/100000000000000000000 : ℝ) := by
    have hpowers : (7357/50000 : ℝ)^4311 ≤ (31345772351093487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7357 : ℕ)^4311*100000000000000000000^1024 ≤ 31345772351093487^1024*50000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7357 50000 31345772351093487 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7357/50000 : ℝ)) (X := (31345772351093487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001966520059725023/10000000000000000000 : ℝ) ≤ (10000467076221151/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (10001966520059725023/10000000000000000000 : ℝ)^1024 ≤ (10000467076221151/10000000000000000 : ℝ)^4311 := by
      have hnat : (10001966520059725023 : ℕ)^1024*10000000000000000^4311 ≤ 10000467076221151^4311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001966520059725023 10000000000000000000 10000467076221151 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000467076221151/10000000000000000 : ℝ)) (X := (10001966520059725023/10000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020589186324859301/50000000000000000000 : ℝ) ≤ (200019559283517/200000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50020589186324859301/50000000000000000000 : ℝ)^1024 ≤ (200019559283517/200000000000000 : ℝ)^4311 := by
      have hnat : (50020589186324859301 : ℕ)^1024*200000000000000^4311 ≤ 200019559283517^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020589186324859301 50000000000000000000 200019559283517 200000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200019559283517/200000000000000 : ℝ)) (X := (50020589186324859301/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031345772351093487/50000000000000000000 : ℝ) ≤ (10001488852130549/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50031345772351093487/50000000000000000000 : ℝ)^1024 ≤ (10001488852130549/10000000000000000 : ℝ)^4311 := by
      have hnat : (50031345772351093487 : ℕ)^1024*10000000000000000^4311 ≤ 10001488852130549^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031345772351093487 50000000000000000000 10001488852130549 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001488852130549/10000000000000000 : ℝ)) (X := (50031345772351093487/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1966520059725023/20000000000000000000 : ℝ) ≤ ((2529302793108251599/2530000000000000000 : ℝ)+2*(510887954699/354200000000000 : ℝ)*(2793/25000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (2529302793108251599/2530000000000000000 : ℝ)+2*(510887954699/354200000000000 : ℝ)*(2793/25000 : ℝ)=(10000467076221151/10000000000000000 : ℝ) by norm_num, show 1+2*(1966520059725023/20000000000000000000 : ℝ)=(10001966520059725023/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31345772351093487/100000000000000000000 : ℝ)+(1966520059725023/20000000000000000000 : ℝ) ≤ ((2529302793108251599/2530000000000000000 : ℝ)+(510887954699/354200000000000 : ℝ)*((7357/50000 : ℝ)+(2793/25000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (2529302793108251599/2530000000000000000 : ℝ)+(510887954699/354200000000000 : ℝ)*((7357/50000 : ℝ)+(2793/25000 : ℝ))=(200019559283517/200000000000000 : ℝ) by norm_num, show 1+(31345772351093487/100000000000000000000 : ℝ)+(1966520059725023/20000000000000000000 : ℝ)=(50020589186324859301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31345772351093487/100000000000000000000 : ℝ) ≤ ((2529302793108251599/2530000000000000000 : ℝ)+2*(510887954699/354200000000000 : ℝ)*(7357/50000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (2529302793108251599/2530000000000000000 : ℝ)+2*(510887954699/354200000000000 : ℝ)*(7357/50000 : ℝ)=(10001488852130549/10000000000000000 : ℝ) by norm_num, show 1+2*(31345772351093487/100000000000000000000 : ℝ)=(50031345772351093487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2529302793108251599/2530000000000000000 : ℝ)*(X 1 0+X 2 0)+(510887954699/354200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (2529302793108251599/2530000000000000000 : ℝ)) (alpha := (510887954699/354200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2529302793108251599/2530000000000000000 : ℝ)*(X 0 1+X 2 1)+(510887954699/354200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (2529302793108251599/2530000000000000000 : ℝ)) (alpha := (510887954699/354200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2529302793108251599/2530000000000000000 : ℝ)*(X 0 2+X 1 2)+(510887954699/354200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (2793/25000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (2529302793108251599/2530000000000000000 : ℝ)) (alpha := (510887954699/354200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-127210309/625000000 : ℝ)*X 0 0+(1353036843/2500000000 : ℝ)*X 0 1+(5244952961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337203201/2500000000 : ℝ)*X 1 0+(-8283371/39062500 : ℝ)*X 1 1+(5244952919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348812763/10000000000 : ℝ)*X 2 0+(5244952991/10000000000 : ℝ)*X 2 1+(-424108587/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162006889/5000000000 : ℝ)*X 0 0+(2075789149/5000000000 : ℝ)*X 0 1+(4503096773/10000000000 : ℝ)*X 0 2+(2162006889/5000000000 : ℝ)*X 1 0+(2075789149/5000000000 : ℝ)*X 1 1+(4503096773/10000000000 : ℝ)*X 1 2+(2162006889/5000000000 : ℝ)*X 2 0+(2075789149/5000000000 : ℝ)*X 2 1+(4503096773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2035377013/10000000000 : ℝ)*X 0 0+(5245551731/10000000000 : ℝ)*X 0 1+(169110797/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652848999/5000000000 : ℝ)*X 1 0+(-7632619/39062500 : ℝ)*X 1 1+(676443183/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061139599/2000000000 : ℝ)*X 2 0+(5411545453/10000000000 : ℝ)*X 2 1+(-488487621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324039271/10000000000 : ℝ)*X 0 0+(2250918963/5000000000 : ℝ)*X 0 1+(4152843481/10000000000 : ℝ)*X 0 2+(4324039271/10000000000 : ℝ)*X 1 0+(2250918963/5000000000 : ℝ)*X 1 1+(4152843481/10000000000 : ℝ)*X 1 2+(4324039271/10000000000 : ℝ)*X 2 0+(2250918963/5000000000 : ℝ)*X 2 1+(4152843481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3023242580829782537831548803/442750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1253695307/100000000000000 : ℝ)*(base19) + (568653733/50000000000000 : ℝ)*(base23) + (37731109/100000000000000 : ℝ)*(lower2) + (1806677/1562500000000 : ℝ)*(upper3) + (52993649/50000000000000 : ℝ)*(upper5) + (2206484803638743/50000000000000 : ℝ)*(major0) + (2206484803638743/50000000000000 : ℝ)*(major1) + (2206484803638743/50000000000000 : ℝ)*(major2) + (2990544077287477/50000000000000 : ℝ)*(sp0) + (2990557118218701/50000000000000 : ℝ)*(sp1) + (5981114352825243/100000000000000 : ℝ)*(sp2) + (56896238332679/2000000000000 : ℝ)*(sp3) + (5467111551/20000000000000 : ℝ)*(sp4) + (11580177351/100000000000000 : ℝ)*(sp7) + (2844823496811301/100000000000000 : ℝ)*(f.failure) + (5981115490132709/100000000000000 : ℝ)*(f.sum) + (3061173128707/8855000000000000000000000000 : ℝ)*base65 + (2526330896530050399/885500000000000000000000000000000 : ℝ)*base67 + (318859037517949601/885500000000000000000000000000000 : ℝ)*base70 + (2282760726574949601/885500000000000000000000000000000 : ℝ)*base72 + (24343519460413/8855000000000000000000000000 : ℝ)*base74 + (832862885680050399/885500000000000000000000000000000 : ℝ)*base75 + (1520566969939550399/885500000000000000000000000000000 : ℝ)*base77 + (1716712030320050399/885500000000000000000000000000000 : ℝ)*base79 + (16700368945877/8855000000000000000000000000 : ℝ)*base81 + (11461091/10000000000000000000000 : ℝ)*base89 + (11461091/10000000000000000000000 : ℝ)*base91 + (11461091/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1129980103948685564203743/110000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1783794619/100000000000000 : ℝ)*(base19) + (493801913/25000000000000 : ℝ)*(base23) + (604283817/100000000000000 : ℝ)*(lower1) + (1901051/1000000000000 : ℝ)*(upper3) + (47491831/50000000000000 : ℝ)*(lower4) + (113327267/50000000000000 : ℝ)*(upper5) + (88896421266163/2000000000000 : ℝ)*(major0) + (88896421266163/2000000000000 : ℝ)*(major1) + (88896421266163/2000000000000 : ℝ)*(major2) + (97200903/5000000000000 : ℝ)*(sp2) + (6024285227205633/100000000000000 : ℝ)*(sp4) + (3012141721705507/50000000000000 : ℝ)*(sp5) + (6024281307979921/100000000000000 : ℝ)*(sp6) + (2865356556992421/100000000000000 : ℝ)*(sp7) + (2865356556992421/100000000000000 : ℝ)*(f.failure) + (6024285227205633/100000000000000 : ℝ)*(f.sum) + (21495983397/11000000000000000000000000 : ℝ)*base66 + (14913118442184581/220000000000000000000000000000 : ℝ)*base68 + (3912012725735419/220000000000000000000000000000 : ℝ)*base69 + (16670534650864581/220000000000000000000000000000 : ℝ)*base72 + (9542451153/2200000000000000000000000 : ℝ)*base74 + (18925975103655419/220000000000000000000000000000 : ℝ)*base75 + (2709373544475419/220000000000000000000000000000 : ℝ)*base77 + (3570893048815419/220000000000000000000000000000 : ℝ)*base79 + (1629380039/5500000000000000000000000 : ℝ)*base81 + (88632989/10000000000000000000000 : ℝ)*base90 + (88632989/10000000000000000000000 : ℝ)*base92 + (88632989/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1352_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1352_s8_0 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348810701/10000000000 : ℝ)*x 0 + (-2120535561/10000000000 : ℝ)*x 1 + (5244960627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348810701/10000000000 : ℝ)^539 ≤ (44017652324449/100000000000000 : ℝ)^411 := by
    have hnat : (5348810701 : ℕ)^539*100000000000000^411 ≤ 44017652324449^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348810701 10000000000 44017652324449 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120535561/10000000000 : ℝ)^539 ≤ (13082079393953/100000000000000 : ℝ)^411 := by
    have hnat : (2120535561 : ℕ)^539*100000000000000^411 ≤ 13082079393953^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120535561 10000000000 13082079393953 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244960627/10000000000 : ℝ)^539 ≤ (5362533532709/12500000000000 : ℝ)^411 := by
    have hnat : (5244960627 : ℕ)^539*12500000000000^411 ≤ 5362533532709^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244960627 10000000000 5362533532709 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348810701/10000000000 : ℝ), (-2120535561/10000000000 : ℝ), (5244960627/10000000000 : ℝ)] ![(44017652324449/100000000000000 : ℝ), (13082079393953/100000000000000 : ℝ), (5362533532709/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348810701/10000000000 : ℝ)|^539 ≤ (44017652324449/100000000000000 : ℝ)^411
        have hw : |(5348810701/10000000000 : ℝ)|=(5348810701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2120535561/10000000000 : ℝ)|^539 ≤ (13082079393953/100000000000000 : ℝ)^411
        have hw : |(-2120535561/10000000000 : ℝ)|=(2120535561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244960627/10000000000 : ℝ)|^539 ≤ (5362533532709/12500000000000 : ℝ)^411
        have hw : |(5244960627/10000000000 : ℝ)|=(5244960627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s8_1 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-127211119/625000000 : ℝ)*x 0 + (655694911/1250000000 : ℝ)*x 1 + (5411537363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127211119/625000000 : ℝ)^539 ≤ (12397455746587/100000000000000 : ℝ)^411 := by
    have hnat : (127211119 : ℕ)^539*100000000000000^411 ≤ 12397455746587^411*625000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127211119 625000000 12397455746587 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655694911/1250000000 : ℝ)^539 ≤ (2145334500591/5000000000000 : ℝ)^411 := by
    have hnat : (655694911 : ℕ)^539*5000000000000^411 ≤ 2145334500591^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655694911 1250000000 2145334500591 5000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411537363/10000000000 : ℝ)^539 ≤ (8939170845891/20000000000000 : ℝ)^411 := by
    have hnat : (5411537363 : ℕ)^539*20000000000000^411 ≤ 8939170845891^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411537363 10000000000 8939170845891 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127211119/625000000 : ℝ), (655694911/1250000000 : ℝ), (5411537363/10000000000 : ℝ)] ![(12397455746587/100000000000000 : ℝ), (2145334500591/5000000000000 : ℝ), (8939170845891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127211119/625000000 : ℝ)|^539 ≤ (12397455746587/100000000000000 : ℝ)^411
        have hw : |(-127211119/625000000 : ℝ)|=(127211119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655694911/1250000000 : ℝ)|^539 ≤ (2145334500591/5000000000000 : ℝ)^411
        have hw : |(655694911/1250000000 : ℝ)|=(655694911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411537363/10000000000 : ℝ)|^539 ≤ (8939170845891/20000000000000 : ℝ)^411
        have hw : |(5411537363/10000000000 : ℝ)|=(5411537363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s8_2 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652850009/5000000000 : ℝ)*x 0 + (-1953958483/10000000000 : ℝ)*x 1 + (5411537617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652850009/5000000000 : ℝ)^539 ≤ (10888242789271/25000000000000 : ℝ)^411 := by
    have hnat : (2652850009 : ℕ)^539*25000000000000^411 ≤ 10888242789271^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652850009 5000000000 10888242789271 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1953958483/10000000000 : ℝ)^539 ≤ (2937792960417/25000000000000 : ℝ)^411 := by
    have hnat : (1953958483 : ℕ)^539*25000000000000^411 ≤ 2937792960417^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953958483 10000000000 2937792960417 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411537617/10000000000 : ℝ)^539 ≤ (44695856980687/100000000000000 : ℝ)^411 := by
    have hnat : (5411537617 : ℕ)^539*100000000000000^411 ≤ 44695856980687^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411537617 10000000000 44695856980687 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652850009/5000000000 : ℝ), (-1953958483/10000000000 : ℝ), (5411537617/10000000000 : ℝ)] ![(10888242789271/25000000000000 : ℝ), (2937792960417/25000000000000 : ℝ), (44695856980687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652850009/5000000000 : ℝ)|^539 ≤ (10888242789271/25000000000000 : ℝ)^411
        have hw : |(2652850009/5000000000 : ℝ)|=(2652850009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1953958483/10000000000 : ℝ)|^539 ≤ (2937792960417/25000000000000 : ℝ)^411
        have hw : |(-1953958483/10000000000 : ℝ)|=(1953958483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411537617/10000000000 : ℝ)|^539 ≤ (44695856980687/100000000000000 : ℝ)^411
        have hw : |(5411537617/10000000000 : ℝ)|=(5411537617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s8_3 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652849909/5000000000 : ℝ)*x 0 + (1352884407/2500000000 : ℝ)*x 1 + (-976979371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652849909/5000000000 : ℝ)^539 ≤ (10888242251011/25000000000000 : ℝ)^411 := by
    have hnat : (2652849909 : ℕ)^539*25000000000000^411 ≤ 10888242251011^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652849909 5000000000 10888242251011 25000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352884407/2500000000 : ℝ)^539 ≤ (8939171419967/20000000000000 : ℝ)^411 := by
    have hnat : (1352884407 : ℕ)^539*20000000000000^411 ≤ 8939171419967^411*2500000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352884407 2500000000 8939171419967 20000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976979371/5000000000 : ℝ)^539 ≤ (5875586942203/50000000000000 : ℝ)^411 := by
    have hnat : (976979371 : ℕ)^539*50000000000000^411 ≤ 5875586942203^411*5000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976979371 5000000000 5875586942203 50000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652849909/5000000000 : ℝ), (1352884407/2500000000 : ℝ), (-976979371/5000000000 : ℝ)] ![(10888242251011/25000000000000 : ℝ), (8939171419967/20000000000000 : ℝ), (5875586942203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652849909/5000000000 : ℝ)|^539 ≤ (10888242251011/25000000000000 : ℝ)^411
        have hw : |(2652849909/5000000000 : ℝ)|=(2652849909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352884407/2500000000 : ℝ)|^539 ≤ (8939171419967/20000000000000 : ℝ)^411
        have hw : |(1352884407/2500000000 : ℝ)|=(1352884407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-976979371/5000000000 : ℝ)|^539 ≤ (5875586942203/50000000000000 : ℝ)^411
        have hw : |(-976979371/5000000000 : ℝ)|=(976979371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1352_s8_4 (p : ℝ) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ)) (x : Fin 3 → ℝ) :
    (540505003/1250000000 : ℝ)*x 0 + (70340957/156250000 : ℝ)*x 1 + (4152859821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540505003/1250000000 : ℝ)^539 ≤ (4162965752363/12500000000000 : ℝ)^411 := by
    have hnat : (540505003 : ℕ)^539*12500000000000^411 ≤ 4162965752363^411*1250000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540505003 1250000000 4162965752363 12500000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70340957/156250000 : ℝ)^539 ≤ (35110824976951/100000000000000 : ℝ)^411 := by
    have hnat : (70340957 : ℕ)^539*100000000000000^411 ≤ 35110824976951^411*156250000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70340957 156250000 35110824976951 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152859821/10000000000 : ℝ)^539 ≤ (31585448988079/100000000000000 : ℝ)^411 := by
    have hnat : (4152859821 : ℕ)^539*100000000000000^411 ≤ 31585448988079^411*10000000000^539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152859821 10000000000 31585448988079 100000000000000 539 411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (539/128 : ℝ)) 539 411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540505003/1250000000 : ℝ), (70340957/156250000 : ℝ), (4152859821/10000000000 : ℝ)] ![(4162965752363/12500000000000 : ℝ), (35110824976951/100000000000000 : ℝ), (31585448988079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540505003/1250000000 : ℝ)|^539 ≤ (4162965752363/12500000000000 : ℝ)^411
        have hw : |(540505003/1250000000 : ℝ)|=(540505003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70340957/156250000 : ℝ)|^539 ≤ (35110824976951/100000000000000 : ℝ)^411
        have hw : |(70340957/156250000 : ℝ)|=(70340957/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152859821/10000000000 : ℝ)|^539 ≤ (31585448988079/100000000000000 : ℝ)^411
        have hw : |(4152859821/10000000000 : ℝ)|=(4152859821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1352_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11173/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1839/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11173/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11173/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11173/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11173/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (9836306063966147/100000000000000000000 : ℝ) := by
    have hpowers : (11173/100000 : ℝ)^4311 ≤ (9836306063966147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11173 : ℕ)^4311*100000000000000000000^1024 ≤ 9836306063966147^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11173 100000 9836306063966147 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11173/100000 : ℝ)) (X := (9836306063966147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14713/100000 : ℝ) ^ (4311/1024 : ℝ) ≤ (31336804695568647/100000000000000000000 : ℝ) := by
    have hpowers : (14713/100000 : ℝ)^4311 ≤ (31336804695568647/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14713 : ℕ)^4311*100000000000000000000^1024 ≤ 31336804695568647^1024*100000^4311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14713 100000 31336804695568647 100000000000000000000 4311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14713/100000 : ℝ)) (X := (31336804695568647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009836306063966147/50000000000000000000 : ℝ) ≤ (10000467252242247/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50009836306063966147/50000000000000000000 : ℝ)^1024 ≤ (10000467252242247/10000000000000000 : ℝ)^4311 := by
      have hnat : (50009836306063966147 : ℕ)^1024*10000000000000000^4311 ≤ 10000467252242247^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009836306063966147 50000000000000000000 10000467252242247 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000467252242247/10000000000000000 : ℝ)) (X := (50009836306063966147/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020586555379767397/50000000000000000000 : ℝ) ≤ (10000977839228401/10000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50020586555379767397/50000000000000000000 : ℝ)^1024 ≤ (10000977839228401/10000000000000000 : ℝ)^4311 := by
      have hnat : (50020586555379767397 : ℕ)^1024*10000000000000000^4311 ≤ 10000977839228401^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020586555379767397 50000000000000000000 10000977839228401 10000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000977839228401/10000000000000000 : ℝ)) (X := (50020586555379767397/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031336804695568647/50000000000000000000 : ℝ) ≤ (2000297685242911/2000000000000000 : ℝ) ^ (4311/1024 : ℝ) := by
    have hpowers : (50031336804695568647/50000000000000000000 : ℝ)^1024 ≤ (2000297685242911/2000000000000000 : ℝ)^4311 := by
      have hnat : (50031336804695568647 : ℕ)^1024*2000000000000000^4311 ≤ 2000297685242911^4311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031336804695568647 50000000000000000000 2000297685242911 2000000000000000 1024 4311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000297685242911/2000000000000000 : ℝ)) (X := (50031336804695568647/50000000000000000000 : ℝ)) (by norm_num) 4311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9836306063966147/100000000000000000000 : ℝ) ≤ ((4423780562018119637/4425000000000000000 : ℝ)+2*(255293493077/177000000000000 : ℝ)*(11173/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (4423780562018119637/4425000000000000000 : ℝ)+2*(255293493077/177000000000000 : ℝ)*(11173/100000 : ℝ)=(10000467252242247/10000000000000000 : ℝ) by norm_num, show 1+2*(9836306063966147/100000000000000000000 : ℝ)=(50009836306063966147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31336804695568647/100000000000000000000 : ℝ)+(9836306063966147/100000000000000000000 : ℝ) ≤ ((4423780562018119637/4425000000000000000 : ℝ)+(255293493077/177000000000000 : ℝ)*((14713/100000 : ℝ)+(11173/100000 : ℝ)))^(4311/1024 : ℝ) := by
    rw [show (4423780562018119637/4425000000000000000 : ℝ)+(255293493077/177000000000000 : ℝ)*((14713/100000 : ℝ)+(11173/100000 : ℝ))=(10000977839228401/10000000000000000 : ℝ) by norm_num, show 1+(31336804695568647/100000000000000000000 : ℝ)+(9836306063966147/100000000000000000000 : ℝ)=(50020586555379767397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31336804695568647/100000000000000000000 : ℝ) ≤ ((4423780562018119637/4425000000000000000 : ℝ)+2*(255293493077/177000000000000 : ℝ)*(14713/100000 : ℝ))^(4311/1024 : ℝ) := by
    rw [show (4423780562018119637/4425000000000000000 : ℝ)+2*(255293493077/177000000000000 : ℝ)*(14713/100000 : ℝ)=(2000297685242911/2000000000000000 : ℝ) by norm_num, show 1+2*(31336804695568647/100000000000000000000 : ℝ)=(50031336804695568647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4423780562018119637/4425000000000000000 : ℝ)*(X 1 0+X 2 0)+(255293493077/177000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (4423780562018119637/4425000000000000000 : ℝ)) (alpha := (255293493077/177000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4423780562018119637/4425000000000000000 : ℝ)*(X 0 1+X 2 1)+(255293493077/177000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (4423780562018119637/4425000000000000000 : ℝ)) (alpha := (255293493077/177000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4423780562018119637/4425000000000000000 : ℝ)*(X 0 2+X 1 2)+(255293493077/177000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4311/1024 : ℝ)) (lo := (11173/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (4423780562018119637/4425000000000000000 : ℝ)) (alpha := (255293493077/177000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348810701/10000000000 : ℝ)*X 1 0+(-2120535561/10000000000 : ℝ)*X 1 1+(5244960627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s8_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-127211119/625000000 : ℝ)*X 0 0+(655694911/1250000000 : ℝ)*X 0 1+(5411537363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2652850009/5000000000 : ℝ)*X 1 0+(-1953958483/10000000000 : ℝ)*X 1 1+(5411537617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652849909/5000000000 : ℝ)*X 2 0+(1352884407/2500000000 : ℝ)*X 2 1+(-976979371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((540505003/1250000000 : ℝ)*X 0 0+(70340957/156250000 : ℝ)*X 0 1+(4152859821/10000000000 : ℝ)*X 0 2+(540505003/1250000000 : ℝ)*X 1 0+(70340957/156250000 : ℝ)*X 1 1+(4152859821/10000000000 : ℝ)*X 1 2+(540505003/1250000000 : ℝ)*X 2 0+(70340957/156250000 : ℝ)*X 2 1+(4152859821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1352_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128382659107626109667670469/73750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117369941/20000000000000 : ℝ)*(base19) + (16495223/5000000000000 : ℝ)*(base23) + (84048117/50000000000000 : ℝ)*(lower1) + (2427797/3125000000000 : ℝ)*(upper3) + (2985413/10000000000000 : ℝ)*(lower4) + (5771227/5000000000000 : ℝ)*(upper5) + (4445259951045263/100000000000000 : ℝ)*(major0) + (4445259951045263/100000000000000 : ℝ)*(major1) + (4445259951045263/100000000000000 : ℝ)*(major2) + (5298450973/50000000000000 : ℝ)*(sp0) + (6024880357829801/100000000000000 : ℝ)*(sp1) + (120497383481563/2000000000000 : ℝ)*(sp2) + (6024880027925341/100000000000000 : ℝ)*(sp3) + (1432819743117329/50000000000000 : ℝ)*(sp4) + (1432819743117329/50000000000000 : ℝ)*(f.failure) + (6024880357829801/100000000000000 : ℝ)*(f.sum) + (6704932844549/8850000000000000000000000000 : ℝ)*base66 + (617261456682404531/442500000000000000000000000000000 : ℝ)*base67 + (3549883221550095469/442500000000000000000000000000000 : ℝ)*base70 + (2177017420227404531/442500000000000000000000000000000 : ℝ)*base71 + (17130501353549/8850000000000000000000000000 : ℝ)*base74 + (2340129785132595469/442500000000000000000000000000000 : ℝ)*base76 + (26309407017404531/442500000000000000000000000000000 : ℝ)*base77 + (1751172370632404531/442500000000000000000000000000000 : ℝ)*base79 + (21889413340349/8850000000000000000000000000 : ℝ)*base82 + (35054761/5000000000000000000000 : ℝ)*base90 + (35054761/5000000000000000000000 : ℝ)*base92 + (35054761/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1352_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1352_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1352_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1352_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1352_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1352_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4311/1024 : ℝ) ≤ p) (hpb : p ≤ (539/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155122791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11173/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1352_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
