-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:10.793652+00:00
-- url     : https://prove2.me/submissions/1d50b03d-5b99-4f97-aa82-7d8d5e0f5b1e

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
theorem support_rectangle_w1138_box_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041779303/10000000000 : ℝ)*x 0 + (5376366413/10000000000 : ℝ)*x 1 + (336022893/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041779303/10000000000 : ℝ)^8331 ≤ (12164660652551/100000000000000 : ℝ)^6283 := by
    have hnat : (2041779303 : ℕ)^8331*100000000000000^6283 ≤ 12164660652551^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041779303 10000000000 12164660652551 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376366413/10000000000 : ℝ)^8331 ≤ (5489708792683/12500000000000 : ℝ)^6283 := by
    have hnat : (5376366413 : ℕ)^8331*12500000000000^6283 ≤ 5489708792683^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376366413 10000000000 5489708792683 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336022893/625000000 : ℝ)^8331 ≤ (1372427155861/3125000000000 : ℝ)^6283 := by
    have hnat : (336022893 : ℕ)^8331*3125000000000^6283 ≤ 1372427155861^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336022893 625000000 1372427155861 3125000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041779303/10000000000 : ℝ), (5376366413/10000000000 : ℝ), (336022893/625000000 : ℝ)] ![(12164660652551/100000000000000 : ℝ), (5489708792683/12500000000000 : ℝ), (1372427155861/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041779303/10000000000 : ℝ)|^8331 ≤ (12164660652551/100000000000000 : ℝ)^6283
        have hw : |(-2041779303/10000000000 : ℝ)|=(2041779303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376366413/10000000000 : ℝ)|^8331 ≤ (5489708792683/12500000000000 : ℝ)^6283
        have hw : |(5376366413/10000000000 : ℝ)|=(5376366413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336022893/625000000 : ℝ)|^8331 ≤ (1372427155861/3125000000000 : ℝ)^6283
        have hw : |(336022893/625000000 : ℝ)|=(336022893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295948389/10000000000 : ℝ)*x 0 + (-86033203/400000000 : ℝ)*x 1 + (2688183167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295948389/10000000000 : ℝ)^8331 ≤ (21524384663679/50000000000000 : ℝ)^6283 := by
    have hnat : (5295948389 : ℕ)^8331*50000000000000^6283 ≤ 21524384663679^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295948389 10000000000 21524384663679 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86033203/400000000 : ℝ)^8331 ≤ (814597573387/6250000000000 : ℝ)^6283 := by
    have hnat : (86033203 : ℕ)^8331*6250000000000^6283 ≤ 814597573387^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86033203 400000000 814597573387 6250000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688183167/5000000000 : ℝ)^8331 ≤ (43917669485791/100000000000000 : ℝ)^6283 := by
    have hnat : (2688183167 : ℕ)^8331*100000000000000^6283 ≤ 43917669485791^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688183167 5000000000 43917669485791 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295948389/10000000000 : ℝ), (-86033203/400000000 : ℝ), (2688183167/5000000000 : ℝ)] ![(21524384663679/50000000000000 : ℝ), (814597573387/6250000000000 : ℝ), (43917669485791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295948389/10000000000 : ℝ)|^8331 ≤ (21524384663679/50000000000000 : ℝ)^6283
        have hw : |(5295948389/10000000000 : ℝ)|=(5295948389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86033203/400000000 : ℝ)|^8331 ≤ (814597573387/6250000000000 : ℝ)^6283
        have hw : |(-86033203/400000000 : ℝ)|=(86033203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688183167/5000000000 : ℝ)|^8331 ≤ (43917669485791/100000000000000 : ℝ)^6283
        have hw : |(2688183167/5000000000 : ℝ)|=(2688183167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647973959/5000000000 : ℝ)*x 0 + (672045799/1250000000 : ℝ)*x 1 + (-2150830629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647973959/5000000000 : ℝ)^8331 ≤ (672636941419/1562500000000 : ℝ)^6283 := by
    have hnat : (2647973959 : ℕ)^8331*1562500000000^6283 ≤ 672636941419^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647973959 5000000000 672636941419 1562500000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672045799/1250000000 : ℝ)^8331 ≤ (43917670114007/100000000000000 : ℝ)^6283 := by
    have hnat : (672045799 : ℕ)^8331*100000000000000^6283 ≤ 43917670114007^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672045799 1250000000 43917670114007 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150830629/10000000000 : ℝ)^8331 ≤ (6516782812797/50000000000000 : ℝ)^6283 := by
    have hnat : (2150830629 : ℕ)^8331*50000000000000^6283 ≤ 6516782812797^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150830629 10000000000 6516782812797 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647973959/5000000000 : ℝ), (672045799/1250000000 : ℝ), (-2150830629/10000000000 : ℝ)] ![(672636941419/1562500000000 : ℝ), (43917670114007/100000000000000 : ℝ), (6516782812797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647973959/5000000000 : ℝ)|^8331 ≤ (672636941419/1562500000000 : ℝ)^6283
        have hw : |(2647973959/5000000000 : ℝ)|=(2647973959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672045799/1250000000 : ℝ)|^8331 ≤ (43917670114007/100000000000000 : ℝ)^6283
        have hw : |(672045799/1250000000 : ℝ)|=(672045799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150830629/10000000000 : ℝ)|^8331 ≤ (6516782812797/50000000000000 : ℝ)^6283
        have hw : |(-2150830629/10000000000 : ℝ)|=(2150830629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4472825099/10000000000 : ℝ)*x 0 + (862711437/2000000000 : ℝ)*x 1 + (4313557301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4472825099/10000000000 : ℝ)^8331 ≤ (17205051365391/50000000000000 : ℝ)^6283 := by
    have hnat : (4472825099 : ℕ)^8331*50000000000000^6283 ≤ 17205051365391^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472825099 10000000000 17205051365391 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862711437/2000000000 : ℝ)^8331 ≤ (16397474022201/50000000000000 : ℝ)^6283 := by
    have hnat : (862711437 : ℕ)^8331*50000000000000^6283 ≤ 16397474022201^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862711437 2000000000 16397474022201 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4313557301/10000000000 : ℝ)^8331 ≤ (32794949213793/100000000000000 : ℝ)^6283 := by
    have hnat : (4313557301 : ℕ)^8331*100000000000000^6283 ≤ 32794949213793^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313557301 10000000000 32794949213793 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4472825099/10000000000 : ℝ), (862711437/2000000000 : ℝ), (4313557301/10000000000 : ℝ)] ![(17205051365391/50000000000000 : ℝ), (16397474022201/50000000000000 : ℝ), (32794949213793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4472825099/10000000000 : ℝ)|^8331 ≤ (17205051365391/50000000000000 : ℝ)^6283
        have hw : |(4472825099/10000000000 : ℝ)|=(4472825099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862711437/2000000000 : ℝ)|^8331 ≤ (16397474022201/50000000000000 : ℝ)^6283
        have hw : |(862711437/2000000000 : ℝ)|=(862711437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4313557301/10000000000 : ℝ)|^8331 ≤ (32794949213793/100000000000000 : ℝ)^6283
        have hw : |(4313557301/10000000000 : ℝ)|=(4313557301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2297211499/10000000000 : ℝ)*x 0 + (5281091767/10000000000 : ℝ)*x 1 + (660136231/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2297211499/10000000000 : ℝ)^8331 ≤ (1777823921889/12500000000000 : ℝ)^6283 := by
    have hnat : (2297211499 : ℕ)^8331*12500000000000^6283 ≤ 1777823921889^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297211499 10000000000 1777823921889 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281091767/10000000000 : ℝ)^8331 ≤ (42888714634193/100000000000000 : ℝ)^6283 := by
    have hnat : (5281091767 : ℕ)^8331*100000000000000^6283 ≤ 42888714634193^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281091767 10000000000 42888714634193 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660136231/1250000000 : ℝ)^8331 ≤ (1072217349243/2500000000000 : ℝ)^6283 := by
    have hnat : (660136231 : ℕ)^8331*2500000000000^6283 ≤ 1072217349243^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660136231 1250000000 1072217349243 2500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2297211499/10000000000 : ℝ), (5281091767/10000000000 : ℝ), (660136231/1250000000 : ℝ)] ![(1777823921889/12500000000000 : ℝ), (42888714634193/100000000000000 : ℝ), (1072217349243/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2297211499/10000000000 : ℝ)|^8331 ≤ (1777823921889/12500000000000 : ℝ)^6283
        have hw : |(-2297211499/10000000000 : ℝ)|=(2297211499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281091767/10000000000 : ℝ)|^8331 ≤ (42888714634193/100000000000000 : ℝ)^6283
        have hw : |(5281091767/10000000000 : ℝ)|=(5281091767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660136231/1250000000 : ℝ)|^8331 ≤ (1072217349243/2500000000000 : ℝ)^6283
        have hw : |(660136231/1250000000 : ℝ)|=(660136231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681633187/5000000000 : ℝ)*x 0 + (-2188297421/10000000000 : ℝ)*x 1 + (211243617/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681633187/5000000000 : ℝ)^8331 ≤ (8755167258257/20000000000000 : ℝ)^6283 := by
    have hnat : (2681633187 : ℕ)^8331*20000000000000^6283 ≤ 8755167258257^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681633187 5000000000 8755167258257 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188297421/10000000000 : ℝ)^8331 ≤ (3333865878349/25000000000000 : ℝ)^6283 := by
    have hnat : (2188297421 : ℕ)^8331*25000000000000^6283 ≤ 3333865878349^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188297421 10000000000 3333865878349 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211243617/400000000 : ℝ)^8331 ≤ (42888700183061/100000000000000 : ℝ)^6283 := by
    have hnat : (211243617 : ℕ)^8331*100000000000000^6283 ≤ 42888700183061^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211243617 400000000 42888700183061 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681633187/5000000000 : ℝ), (-2188297421/10000000000 : ℝ), (211243617/400000000 : ℝ)] ![(8755167258257/20000000000000 : ℝ), (3333865878349/25000000000000 : ℝ), (42888700183061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681633187/5000000000 : ℝ)|^8331 ≤ (8755167258257/20000000000000 : ℝ)^6283
        have hw : |(2681633187/5000000000 : ℝ)|=(2681633187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188297421/10000000000 : ℝ)|^8331 ≤ (3333865878349/25000000000000 : ℝ)^6283
        have hw : |(-2188297421/10000000000 : ℝ)|=(2188297421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211243617/400000000 : ℝ)|^8331 ≤ (42888700183061/100000000000000 : ℝ)^6283
        have hw : |(211243617/400000000 : ℝ)|=(211243617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681633337/5000000000 : ℝ)*x 0 + (330068141/625000000 : ℝ)*x 1 + (-547074311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681633337/5000000000 : ℝ)^8331 ≤ (43775839538091/100000000000000 : ℝ)^6283 := by
    have hnat : (2681633337 : ℕ)^8331*100000000000000^6283 ≤ 43775839538091^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681633337 5000000000 43775839538091 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330068141/625000000 : ℝ)^8331 ≤ (42888698363209/100000000000000 : ℝ)^6283 := by
    have hnat : (330068141 : ℕ)^8331*100000000000000^6283 ≤ 42888698363209^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330068141 625000000 42888698363209 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547074311/2500000000 : ℝ)^8331 ≤ (13335462083169/100000000000000 : ℝ)^6283 := by
    have hnat : (547074311 : ℕ)^8331*100000000000000^6283 ≤ 13335462083169^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547074311 2500000000 13335462083169 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681633337/5000000000 : ℝ), (330068141/625000000 : ℝ), (-547074311/2500000000 : ℝ)] ![(43775839538091/100000000000000 : ℝ), (42888698363209/100000000000000 : ℝ), (13335462083169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681633337/5000000000 : ℝ)|^8331 ≤ (43775839538091/100000000000000 : ℝ)^6283
        have hw : |(2681633337/5000000000 : ℝ)|=(2681633337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330068141/625000000 : ℝ)|^8331 ≤ (42888698363209/100000000000000 : ℝ)^6283
        have hw : |(330068141/625000000 : ℝ)|=(330068141/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547074311/2500000000 : ℝ)|^8331 ≤ (13335462083169/100000000000000 : ℝ)^6283
        have hw : |(-547074311/2500000000 : ℝ)|=(547074311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1064323457/2500000000 : ℝ)*x 0 + (552662691/1250000000 : ℝ)*x 1 + (2210651243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064323457/2500000000 : ℝ)^8331 ≤ (4028621154603/12500000000000 : ℝ)^6283 := by
    have hnat : (1064323457 : ℕ)^8331*12500000000000^6283 ≤ 4028621154603^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064323457 2500000000 4028621154603 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552662691/1250000000 : ℝ)^8331 ≤ (33885510508067/100000000000000 : ℝ)^6283 := by
    have hnat : (552662691 : ℕ)^8331*100000000000000^6283 ≤ 33885510508067^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552662691 1250000000 33885510508067 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210651243/5000000000 : ℝ)^8331 ≤ (6777104048719/20000000000000 : ℝ)^6283 := by
    have hnat : (2210651243 : ℕ)^8331*20000000000000^6283 ≤ 6777104048719^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210651243 5000000000 6777104048719 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064323457/2500000000 : ℝ), (552662691/1250000000 : ℝ), (2210651243/5000000000 : ℝ)] ![(4028621154603/12500000000000 : ℝ), (33885510508067/100000000000000 : ℝ), (6777104048719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064323457/2500000000 : ℝ)|^8331 ≤ (4028621154603/12500000000000 : ℝ)^6283
        have hw : |(1064323457/2500000000 : ℝ)|=(1064323457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552662691/1250000000 : ℝ)|^8331 ≤ (33885510508067/100000000000000 : ℝ)^6283
        have hw : |(552662691/1250000000 : ℝ)|=(552662691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210651243/5000000000 : ℝ)|^8331 ≤ (6777104048719/20000000000000 : ℝ)^6283
        have hw : |(2210651243/5000000000 : ℝ)|=(2210651243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_8 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-448760293/2000000000 : ℝ)*x 0 + (1043260301/2000000000 : ℝ)*x 1 + (5385974637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448760293/2000000000 : ℝ)^8331 ≤ (6892900437603/50000000000000 : ℝ)^6283 := by
    have hnat : (448760293 : ℕ)^8331*50000000000000^6283 ≤ 6892900437603^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448760293 2000000000 6892900437603 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043260301/2000000000 : ℝ)^8331 ≤ (10548107231677/25000000000000 : ℝ)^6283 := by
    have hnat : (1043260301 : ℕ)^8331*25000000000000^6283 ≤ 10548107231677^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043260301 2000000000 10548107231677 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385974637/10000000000 : ℝ)^8331 ≤ (11005442544919/25000000000000 : ℝ)^6283 := by
    have hnat : (5385974637 : ℕ)^8331*25000000000000^6283 ≤ 11005442544919^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385974637 10000000000 11005442544919 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448760293/2000000000 : ℝ), (1043260301/2000000000 : ℝ), (5385974637/10000000000 : ℝ)] ![(6892900437603/50000000000000 : ℝ), (10548107231677/25000000000000 : ℝ), (11005442544919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448760293/2000000000 : ℝ)|^8331 ≤ (6892900437603/50000000000000 : ℝ)^6283
        have hw : |(-448760293/2000000000 : ℝ)|=(448760293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043260301/2000000000 : ℝ)|^8331 ≤ (10548107231677/25000000000000 : ℝ)^6283
        have hw : |(1043260301/2000000000 : ℝ)|=(1043260301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385974637/10000000000 : ℝ)|^8331 ≤ (11005442544919/25000000000000 : ℝ)^6283
        have hw : |(5385974637/10000000000 : ℝ)|=(5385974637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_9 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289155851/10000000000 : ℝ)*x 0 + (-1073491399/5000000000 : ℝ)*x 1 + (2692987291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289155851/10000000000 : ℝ)^8331 ≤ (42975573162117/100000000000000 : ℝ)^6283 := by
    have hnat : (5289155851 : ℕ)^8331*100000000000000^6283 ≤ 42975573162117^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289155851 10000000000 42975573162117 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073491399/5000000000 : ℝ)^8331 ≤ (13002657234569/100000000000000 : ℝ)^6283 := by
    have hnat : (1073491399 : ℕ)^8331*100000000000000^6283 ≤ 13002657234569^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073491399 5000000000 13002657234569 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692987291/5000000000 : ℝ)^8331 ≤ (5502721197951/12500000000000 : ℝ)^6283 := by
    have hnat : (2692987291 : ℕ)^8331*12500000000000^6283 ≤ 5502721197951^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692987291 5000000000 5502721197951 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289155851/10000000000 : ℝ), (-1073491399/5000000000 : ℝ), (2692987291/5000000000 : ℝ)] ![(42975573162117/100000000000000 : ℝ), (13002657234569/100000000000000 : ℝ), (5502721197951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289155851/10000000000 : ℝ)|^8331 ≤ (42975573162117/100000000000000 : ℝ)^6283
        have hw : |(5289155851/10000000000 : ℝ)|=(5289155851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073491399/5000000000 : ℝ)|^8331 ≤ (13002657234569/100000000000000 : ℝ)^6283
        have hw : |(-1073491399/5000000000 : ℝ)|=(1073491399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692987291/5000000000 : ℝ)|^8331 ≤ (5502721197951/12500000000000 : ℝ)^6283
        have hw : |(2692987291/5000000000 : ℝ)|=(2692987291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_10 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057831173/2000000000 : ℝ)*x 0 + (538597463/1000000000 : ℝ)*x 1 + (-429396543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057831173/2000000000 : ℝ)^8331 ≤ (42975573312949/100000000000000 : ℝ)^6283 := by
    have hnat : (1057831173 : ℕ)^8331*100000000000000^6283 ≤ 42975573312949^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057831173 2000000000 42975573312949 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538597463/1000000000 : ℝ)^8331 ≤ (44021770103813/100000000000000 : ℝ)^6283 := by
    have hnat : (538597463 : ℕ)^8331*100000000000000^6283 ≤ 44021770103813^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538597463 1000000000 44021770103813 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429396543/2000000000 : ℝ)^8331 ≤ (13002656568051/100000000000000 : ℝ)^6283 := by
    have hnat : (429396543 : ℕ)^8331*100000000000000^6283 ≤ 13002656568051^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429396543 2000000000 13002656568051 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057831173/2000000000 : ℝ), (538597463/1000000000 : ℝ), (-429396543/2000000000 : ℝ)] ![(42975573312949/100000000000000 : ℝ), (44021770103813/100000000000000 : ℝ), (13002656568051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057831173/2000000000 : ℝ)|^8331 ≤ (42975573312949/100000000000000 : ℝ)^6283
        have hw : |(1057831173/2000000000 : ℝ)|=(1057831173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538597463/1000000000 : ℝ)|^8331 ≤ (44021770103813/100000000000000 : ℝ)^6283
        have hw : |(538597463/1000000000 : ℝ)|=(538597463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429396543/2000000000 : ℝ)|^8331 ≤ (13002656568051/100000000000000 : ℝ)^6283
        have hw : |(-429396543/2000000000 : ℝ)|=(429396543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_11 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2247143907/5000000000 : ℝ)*x 0 + (4302685283/10000000000 : ℝ)*x 1 + (172107417/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2247143907/5000000000 : ℝ)^8331 ≤ (34629210576739/100000000000000 : ℝ)^6283 := by
    have hnat : (2247143907 : ℕ)^8331*100000000000000^6283 ≤ 34629210576739^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247143907 5000000000 34629210576739 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4302685283/10000000000 : ℝ)^8331 ≤ (16342696994781/50000000000000 : ℝ)^6283 := by
    have hnat : (4302685283 : ℕ)^8331*50000000000000^6283 ≤ 16342696994781^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302685283 10000000000 16342696994781 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172107417/400000000 : ℝ)^8331 ≤ (817134885497/2500000000000 : ℝ)^6283 := by
    have hnat : (172107417 : ℕ)^8331*2500000000000^6283 ≤ 817134885497^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172107417 400000000 817134885497 2500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2247143907/5000000000 : ℝ), (4302685283/10000000000 : ℝ), (172107417/400000000 : ℝ)] ![(34629210576739/100000000000000 : ℝ), (16342696994781/50000000000000 : ℝ), (817134885497/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2247143907/5000000000 : ℝ)|^8331 ≤ (34629210576739/100000000000000 : ℝ)^6283
        have hw : |(2247143907/5000000000 : ℝ)|=(2247143907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4302685283/10000000000 : ℝ)|^8331 ≤ (16342696994781/50000000000000 : ℝ)^6283
        have hw : |(4302685283/10000000000 : ℝ)|=(4302685283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172107417/400000000 : ℝ)|^8331 ≤ (817134885497/2500000000000 : ℝ)^6283
        have hw : |(172107417/400000000 : ℝ)|=(172107417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_12 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095511539/10000000000 : ℝ)*x 0 + (5439874741/10000000000 : ℝ)*x 1 + (5273053911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095511539/10000000000 : ℝ)^8331 ≤ (12590949587817/100000000000000 : ℝ)^6283 := by
    have hnat : (2095511539 : ℕ)^8331*100000000000000^6283 ≤ 12590949587817^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095511539 10000000000 12590949587817 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439874741/10000000000 : ℝ)^8331 ≤ (348491162319/781250000000 : ℝ)^6283 := by
    have hnat : (5439874741 : ℕ)^8331*781250000000^6283 ≤ 348491162319^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439874741 10000000000 348491162319 781250000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273053911/10000000000 : ℝ)^8331 ≤ (10700545404919/25000000000000 : ℝ)^6283 := by
    have hnat : (5273053911 : ℕ)^8331*25000000000000^6283 ≤ 10700545404919^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273053911 10000000000 10700545404919 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095511539/10000000000 : ℝ), (5439874741/10000000000 : ℝ), (5273053911/10000000000 : ℝ)] ![(12590949587817/100000000000000 : ℝ), (348491162319/781250000000 : ℝ), (10700545404919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095511539/10000000000 : ℝ)|^8331 ≤ (12590949587817/100000000000000 : ℝ)^6283
        have hw : |(-2095511539/10000000000 : ℝ)|=(2095511539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439874741/10000000000 : ℝ)|^8331 ≤ (348491162319/781250000000 : ℝ)^6283
        have hw : |(5439874741/10000000000 : ℝ)|=(5439874741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273053911/10000000000 : ℝ)|^8331 ≤ (10700545404919/25000000000000 : ℝ)^6283
        have hw : |(5273053911/10000000000 : ℝ)|=(5273053911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_13 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073788583/2000000000 : ℝ)*x 0 + (-54785003/250000000 : ℝ)*x 1 + (1318263379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073788583/2000000000 : ℝ)^8331 ≤ (1369915072543/3125000000000 : ℝ)^6283 := by
    have hnat : (1073788583 : ℕ)^8331*3125000000000^6283 ≤ 1369915072543^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073788583 2000000000 1369915072543 3125000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54785003/250000000 : ℝ)^8331 ≤ (1670067536903/12500000000000 : ℝ)^6283 := by
    have hnat : (54785003 : ℕ)^8331*12500000000000^6283 ≤ 1670067536903^6283*250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54785003 250000000 1670067536903 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318263379/2500000000 : ℝ)^8331 ≤ (42802177368287/100000000000000 : ℝ)^6283 := by
    have hnat : (1318263379 : ℕ)^8331*100000000000000^6283 ≤ 42802177368287^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318263379 2500000000 42802177368287 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073788583/2000000000 : ℝ), (-54785003/250000000 : ℝ), (1318263379/2500000000 : ℝ)] ![(1369915072543/3125000000000 : ℝ), (1670067536903/12500000000000 : ℝ), (42802177368287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073788583/2000000000 : ℝ)|^8331 ≤ (1369915072543/3125000000000 : ℝ)^6283
        have hw : |(1073788583/2000000000 : ℝ)|=(1073788583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54785003/250000000 : ℝ)|^8331 ≤ (1670067536903/12500000000000 : ℝ)^6283
        have hw : |(-54785003/250000000 : ℝ)|=(54785003/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318263379/2500000000 : ℝ)|^8331 ≤ (42802177368287/100000000000000 : ℝ)^6283
        have hw : |(1318263379/2500000000 : ℝ)|=(1318263379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_14 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684471311/5000000000 : ℝ)*x 0 + (1318263513/2500000000 : ℝ)*x 1 + (-2191399799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684471311/5000000000 : ℝ)^8331 ≤ (8767455829847/20000000000000 : ℝ)^6283 := by
    have hnat : (2684471311 : ℕ)^8331*20000000000000^6283 ≤ 8767455829847^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684471311 5000000000 8767455829847 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318263513/2500000000 : ℝ)^8331 ≤ (42802183137261/100000000000000 : ℝ)^6283 := by
    have hnat : (1318263513 : ℕ)^8331*100000000000000^6283 ≤ 42802183137261^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318263513 2500000000 42802183137261 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191399799/10000000000 : ℝ)^8331 ≤ (104379200783/781250000000 : ℝ)^6283 := by
    have hnat : (2191399799 : ℕ)^8331*781250000000^6283 ≤ 104379200783^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191399799 10000000000 104379200783 781250000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684471311/5000000000 : ℝ), (1318263513/2500000000 : ℝ), (-2191399799/10000000000 : ℝ)] ![(8767455829847/20000000000000 : ℝ), (42802183137261/100000000000000 : ℝ), (104379200783/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684471311/5000000000 : ℝ)|^8331 ≤ (8767455829847/20000000000000 : ℝ)^6283
        have hw : |(2684471311/5000000000 : ℝ)|=(2684471311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318263513/2500000000 : ℝ)|^8331 ≤ (42802183137261/100000000000000 : ℝ)^6283
        have hw : |(1318263513/2500000000 : ℝ)|=(1318263513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191399799/10000000000 : ℝ)|^8331 ≤ (104379200783/781250000000 : ℝ)^6283
        have hw : |(-2191399799/10000000000 : ℝ)|=(2191399799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_box_15 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529860319/1250000000 : ℝ)*x 0 + (2215192751/5000000000 : ℝ)*x 1 + (553798177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529860319/1250000000 : ℝ)^8331 ≤ (1602214453781/5000000000000 : ℝ)^6283 := by
    have hnat : (529860319 : ℕ)^8331*5000000000000^6283 ≤ 1602214453781^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529860319 1250000000 1602214453781 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2215192751/5000000000 : ℝ)^8331 ≤ (33977855891907/100000000000000 : ℝ)^6283 := by
    have hnat : (2215192751 : ℕ)^8331*100000000000000^6283 ≤ 33977855891907^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215192751 5000000000 33977855891907 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553798177/1250000000 : ℝ)^8331 ≤ (424723187717/1250000000000 : ℝ)^6283 := by
    have hnat : (553798177 : ℕ)^8331*1250000000000^6283 ≤ 424723187717^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553798177 1250000000 424723187717 1250000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529860319/1250000000 : ℝ), (2215192751/5000000000 : ℝ), (553798177/1250000000 : ℝ)] ![(1602214453781/5000000000000 : ℝ), (33977855891907/100000000000000 : ℝ), (424723187717/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529860319/1250000000 : ℝ)|^8331 ≤ (1602214453781/5000000000000 : ℝ)^6283
        have hw : |(529860319/1250000000 : ℝ)|=(529860319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2215192751/5000000000 : ℝ)|^8331 ≤ (33977855891907/100000000000000 : ℝ)^6283
        have hw : |(2215192751/5000000000 : ℝ)|=(2215192751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553798177/1250000000 : ℝ)|^8331 ≤ (424723187717/1250000000000 : ℝ)^6283
        have hw : |(553798177/1250000000 : ℝ)|=(553798177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62231/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11859/20000 : ℝ) ∧ (19949/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16623/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11349/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (55964264902857/390625000000000000 : ℝ) := by
    have hpowers : (11349/100000 : ℝ)^4165 ≤ (55964264902857/390625000000000000 : ℝ)^1024 := by
      have hnat : (11349 : ℕ)^4165*390625000000000000^1024 ≤ 55964264902857^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11349 100000 55964264902857 390625000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11349/100000 : ℝ)) (X := (55964264902857/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7023/50000 : ℝ) ^ (4165/1024 : ℝ) ≤ (34101254611717051/100000000000000000000 : ℝ) := by
    have hpowers : (7023/50000 : ℝ)^4165 ≤ (34101254611717051/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7023 : ℕ)^4165*100000000000000000000^1024 ≤ 34101254611717051^1024*50000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7023 50000 34101254611717051 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7023/50000 : ℝ)) (X := (34101254611717051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (195368464264902857/195312500000000000 : ℝ) ≤ (10000704399108399/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (195368464264902857/195312500000000000 : ℝ)^1024 ≤ (10000704399108399/10000000000000000 : ℝ)^4165 := by
      have hnat : (195368464264902857 : ℕ)^1024*10000000000000000^4165 ≤ 10000704399108399^4165*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195368464264902857 195312500000000000 10000704399108399 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000704399108399/10000000000000000 : ℝ)) (X := (195368464264902857/195312500000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048428106426848443/100000000000000000000 : ℝ) ≤ (5000595214020783/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (100048428106426848443/100000000000000000000 : ℝ)^1024 ≤ (5000595214020783/5000000000000000 : ℝ)^4165 := by
      have hnat : (100048428106426848443 : ℕ)^1024*5000000000000000^4165 ≤ 5000595214020783^4165*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048428106426848443 100000000000000000000 5000595214020783 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000595214020783/5000000000000000 : ℝ)) (X := (100048428106426848443/100000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034101254611717051/50000000000000000000 : ℝ) ≤ (10001676456974733/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50034101254611717051/50000000000000000000 : ℝ)^1024 ≤ (10001676456974733/10000000000000000 : ℝ)^4165 := by
      have hnat : (50034101254611717051 : ℕ)^1024*10000000000000000^4165 ≤ 10001676456974733^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034101254611717051 50000000000000000000 10001676456974733 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001676456974733/10000000000000000 : ℝ)) (X := (50034101254611717051/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(55964264902857/390625000000000000 : ℝ) ≤ ((8986955959890109179/8990000000000000000 : ℝ)+2*(162009644389/89900000000000 : ℝ)*(11349/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (8986955959890109179/8990000000000000000 : ℝ)+2*(162009644389/89900000000000 : ℝ)*(11349/100000 : ℝ)=(10000704399108399/10000000000000000 : ℝ) by norm_num, show 1+2*(55964264902857/390625000000000000 : ℝ)=(195368464264902857/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34101254611717051/100000000000000000000 : ℝ)+(55964264902857/390625000000000000 : ℝ) ≤ ((8986955959890109179/8990000000000000000 : ℝ)+(162009644389/89900000000000 : ℝ)*((7023/50000 : ℝ)+(11349/100000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (8986955959890109179/8990000000000000000 : ℝ)+(162009644389/89900000000000 : ℝ)*((7023/50000 : ℝ)+(11349/100000 : ℝ))=(5000595214020783/5000000000000000 : ℝ) by norm_num, show 1+(34101254611717051/100000000000000000000 : ℝ)+(55964264902857/390625000000000000 : ℝ)=(100048428106426848443/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34101254611717051/100000000000000000000 : ℝ) ≤ ((8986955959890109179/8990000000000000000 : ℝ)+2*(162009644389/89900000000000 : ℝ)*(7023/50000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (8986955959890109179/8990000000000000000 : ℝ)+2*(162009644389/89900000000000 : ℝ)*(7023/50000 : ℝ)=(10001676456974733/10000000000000000 : ℝ) by norm_num, show 1+2*(34101254611717051/100000000000000000000 : ℝ)=(50034101254611717051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8986955959890109179/8990000000000000000 : ℝ)*(X 1 0+X 2 0)+(162009644389/89900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (8986955959890109179/8990000000000000000 : ℝ)) (alpha := (162009644389/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8986955959890109179/8990000000000000000 : ℝ)*(X 0 1+X 2 1)+(162009644389/89900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (8986955959890109179/8990000000000000000 : ℝ)) (alpha := (162009644389/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8986955959890109179/8990000000000000000 : ℝ)*(X 0 2+X 1 2)+(162009644389/89900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7023/50000 : ℝ)) (c := (8986955959890109179/8990000000000000000 : ℝ)) (alpha := (162009644389/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2041779303/10000000000 : ℝ)*X 0 0+(5376366413/10000000000 : ℝ)*X 0 1+(336022893/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295948389/10000000000 : ℝ)*X 1 0+(-86033203/400000000 : ℝ)*X 1 1+(2688183167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647973959/5000000000 : ℝ)*X 2 0+(672045799/1250000000 : ℝ)*X 2 1+(-2150830629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4472825099/10000000000 : ℝ)*X 0 0+(862711437/2000000000 : ℝ)*X 0 1+(4313557301/10000000000 : ℝ)*X 0 2+(4472825099/10000000000 : ℝ)*X 1 0+(862711437/2000000000 : ℝ)*X 1 1+(4313557301/10000000000 : ℝ)*X 1 2+(4472825099/10000000000 : ℝ)*X 2 0+(862711437/2000000000 : ℝ)*X 2 1+(4313557301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2297211499/10000000000 : ℝ)*X 0 0+(5281091767/10000000000 : ℝ)*X 0 1+(660136231/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681633187/5000000000 : ℝ)*X 1 0+(-2188297421/10000000000 : ℝ)*X 1 1+(211243617/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681633337/5000000000 : ℝ)*X 2 0+(330068141/625000000 : ℝ)*X 2 1+(-547074311/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1064323457/2500000000 : ℝ)*X 0 0+(552662691/1250000000 : ℝ)*X 0 1+(2210651243/5000000000 : ℝ)*X 0 2+(1064323457/2500000000 : ℝ)*X 1 0+(552662691/1250000000 : ℝ)*X 1 1+(2210651243/5000000000 : ℝ)*X 1 2+(1064323457/2500000000 : ℝ)*X 2 0+(552662691/1250000000 : ℝ)*X 2 1+(2210651243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-448760293/2000000000 : ℝ)*X 0 0+(1043260301/2000000000 : ℝ)*X 0 1+(5385974637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289155851/10000000000 : ℝ)*X 1 0+(-1073491399/5000000000 : ℝ)*X 1 1+(2692987291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057831173/2000000000 : ℝ)*X 2 0+(538597463/1000000000 : ℝ)*X 2 1+(-429396543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2247143907/5000000000 : ℝ)*X 0 0+(4302685283/10000000000 : ℝ)*X 0 1+(172107417/400000000 : ℝ)*X 0 2+(2247143907/5000000000 : ℝ)*X 1 0+(4302685283/10000000000 : ℝ)*X 1 1+(172107417/400000000 : ℝ)*X 1 2+(2247143907/5000000000 : ℝ)*X 2 0+(4302685283/10000000000 : ℝ)*X 2 1+(172107417/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2095511539/10000000000 : ℝ)*X 0 0+(5439874741/10000000000 : ℝ)*X 0 1+(5273053911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073788583/2000000000 : ℝ)*X 1 0+(-54785003/250000000 : ℝ)*X 1 1+(1318263379/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684471311/5000000000 : ℝ)*X 2 0+(1318263513/2500000000 : ℝ)*X 2 1+(-2191399799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((529860319/1250000000 : ℝ)*X 0 0+(2215192751/5000000000 : ℝ)*X 0 1+(553798177/1250000000 : ℝ)*X 0 2+(529860319/1250000000 : ℝ)*X 1 0+(2215192751/5000000000 : ℝ)*X 1 1+(553798177/1250000000 : ℝ)*X 1 2+(529860319/1250000000 : ℝ)*X 2 0+(2215192751/5000000000 : ℝ)*X 2 1+(553798177/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62231/100000 : ℝ) ≤ (-69928830161808612441128635612329/112375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73859261/25000000000000 : ℝ)*(upper0) + (141691361/100000000000000 : ℝ)*(lower2) + (56896659/100000000000000 : ℝ)*(lower3) + (1958615080256617/50000000000000 : ℝ)*(major0) + (1958615080256617/50000000000000 : ℝ)*(major1) + (1958615080256617/50000000000000 : ℝ)*(major2) + (16347426303/100000000000000 : ℝ)*(sp1) + (290945079/1562500000000 : ℝ)*(sp2) + (8745357463/100000000000000 : ℝ)*(sp3) + (5233103274632121/100000000000000 : ℝ)*(sp4) + (5233135990672881/100000000000000 : ℝ)*(sp5) + (327070857350883/6250000000000 : ℝ)*(sp6) + (2622041938396451/100000000000000 : ℝ)*(sp7) + (49063467063/100000000000000 : ℝ)*(sp8) + (1311025341876957/50000000000000 : ℝ)*(f.failure) + (1046630467619837/20000000000000 : ℝ)*(f.sum) + (23661668007519/4495000000000000000000000000 : ℝ)*base66 + (2368600362620987443/449500000000000000000000000000000 : ℝ)*base67 + (3768218903712487443/449500000000000000000000000000000 : ℝ)*base69 + (2657327148781487443/449500000000000000000000000000000 : ℝ)*base71 + (40336025881689/4495000000000000000000000000 : ℝ)*base74 + (4037532833556487443/449500000000000000000000000000000 : ℝ)*base75 + (2658583807390987443/449500000000000000000000000000000 : ℝ)*base77 + (1835886482930012557/449500000000000000000000000000000 : ℝ)*base80 + (6584081969009/4495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6699233/5000000000000000000000 : ℝ)*base89 + (6699233/5000000000000000000000 : ℝ)*base91 + (6699233/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11859/20000 : ℝ) ≤ (133271966103388517878558039062681/224750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1044519/1562500000000 : ℝ)*(lower0) + (314687903/100000000000000 : ℝ)*(upper2) + (26165531/100000000000000 : ℝ)*(lower4) + (35820123/25000000000000 : ℝ)*(lower5) + (1990650306675629/50000000000000 : ℝ)*(major0) + (1990650306675629/50000000000000 : ℝ)*(major1) + (1990650306675629/50000000000000 : ℝ)*(major2) + (1319471969248639/25000000000000 : ℝ)*(sp0) + (1055576892171503/20000000000000 : ℝ)*(sp1) + (5277898166619769/100000000000000 : ℝ)*(sp2) + (666232118063627/25000000000000 : ℝ)*(sp3) + (6852881127/50000000000000 : ℝ)*(sp5) + (1726135067/20000000000000 : ℝ)*(sp7) + (2572406303/25000000000000 : ℝ)*(sp12) + (2664937102929843/100000000000000 : ℝ)*(f.failure) + (5277898166619769/100000000000000 : ℝ)*(f.sum) + (10800936627979/2247500000000000000000000000 : ℝ)*base66 + (8355551066706598591/449500000000000000000000000000000 : ℝ)*base67 + (4693965241805598591/449500000000000000000000000000000 : ℝ)*base69 + (3554891326068098591/449500000000000000000000000000000 : ℝ)*base71 + (23480691643367/4495000000000000000000000000 : ℝ)*base73 + (3415593669655598591/449500000000000000000000000000000 : ℝ)*base75 + (995550426423598591/449500000000000000000000000000000 : ℝ)*base77 + (3448545781970598591/449500000000000000000000000000000 : ℝ)*base79 + (8982070419947/4495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (44950033/10000000000000000000000 : ℝ)*base90 + (44950033/10000000000000000000000 : ℝ)*base92 + (44950033/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (19949/25000 : ℝ) ≤ (3586940878686857269546854231/4495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11619289/50000000000000 : ℝ)*(upper0) + (15075051/25000000000000 : ℝ)*(lower3) + (10890139/50000000000000 : ℝ)*(upper4) + (2224607177759233/50000000000000 : ℝ)*(major0) + (2224607177759233/50000000000000 : ℝ)*(major1) + (2224607177759233/50000000000000 : ℝ)*(major2) + (4079675457/10000000000000 : ℝ)*(sp1) + (7589838029/12500000000000 : ℝ)*(sp2) + (2059402393/12500000000000 : ℝ)*(sp3) + (539335163/50000000000000 : ℝ)*(sp4) + (5893686686562303/100000000000000 : ℝ)*(sp8) + (294682348423903/5000000000000 : ℝ)*(sp9) + (2946813523264199/50000000000000 : ℝ)*(sp10) + (297812498316441/10000000000000 : ℝ)*(sp11) + (1489070729191777/50000000000000 : ℝ)*(f.failure) + (589368776523263/10000000000000 : ℝ)*(f.sum) + (13257420422091/4495000000000000000000000000 : ℝ)*base66 + (2840129662977500293/449500000000000000000000000000000 : ℝ)*base68 + (1505633532514500293/449500000000000000000000000000000 : ℝ)*base70 + (37788666501999707/449500000000000000000000000000000 : ℝ)*base71 + (38294817888763/2247500000000000000000000000 : ℝ)*base74 + (1938634217955999707/449500000000000000000000000000000 : ℝ)*base75 + (76800775470000293/449500000000000000000000000000000 : ℝ)*base78 + (7249103875685999707/449500000000000000000000000000000 : ℝ)*base79 + (8413651492123/2247500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (54213813/5000000000000000000000 : ℝ)*base89 + (54213813/5000000000000000000000 : ℝ)*base91 + (54213813/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-16623/20000 : ℝ) ≤ (-18679640630792667767735573385717/22475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11991699/100000000000000 : ℝ)*(lower0) + (163133/500000000000 : ℝ)*(lower1) + (91436253/100000000000000 : ℝ)*(lower2) + (224207103869141/5000000000000 : ℝ)*(major0) + (224207103869141/5000000000000 : ℝ)*(major1) + (224207103869141/5000000000000 : ℝ)*(major2) + (2920159343/20000000000000 : ℝ)*(sp0) + (65362873671/12500000000000 : ℝ)*(sp5) + (52420969753/100000000000000 : ℝ)*(sp6) + (26187860141/100000000000000 : ℝ)*(sp7) + (5994453079532821/100000000000000 : ℝ)*(sp12) + (749243097167521/12500000000000 : ℝ)*(sp13) + (5994415259359783/100000000000000 : ℝ)*(sp14) + (3001494610833709/100000000000000 : ℝ)*(sp15) + (60030415973877/2000000000000 : ℝ)*(f.failure) + (5994467680329537/100000000000000 : ℝ)*(f.sum) + (561845496637/224750000000000000000000000 : ℝ)*base65 + (259635931314945239/44950000000000000000000000000000 : ℝ)*base67 + (187825371124895239/44950000000000000000000000000000 : ℝ)*base69 + (78508824432754761/44950000000000000000000000000000 : ℝ)*base72 + (13084302395737/449500000000000000000000000 : ℝ)*base73 + (505712884221745239/44950000000000000000000000000000 : ℝ)*base75 + (51802285192954761/44950000000000000000000000000000 : ℝ)*base78 + (317715384546345239/44950000000000000000000000000000 : ℝ)*base79 + (2410721144617/899000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (938713/200000000000000000000 : ℝ)*base89 + (938713/200000000000000000000 : ℝ)*base91 + (938713/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1138_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11859/20000 : ℝ) else (19949/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16623/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1138_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1138_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11859/20000 : ℝ) else (19949/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16623/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1138_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11859/20000 : ℝ) else (19949/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16623/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
