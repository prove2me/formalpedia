-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1555_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:11:22.285617+00:00
-- url     : https://prove2.me/submissions/ffe1fc41-c29b-469e-bb10-a3c2579b8c86

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
theorem support_rectangle_w1555_s3_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1806015053/10000000000 : ℝ)*x 0 + (2714844459/5000000000 : ℝ)*x 1 + (5217731211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806015053/10000000000 : ℝ)^4607 ≤ (2768450611237/25000000000000 : ℝ)^3583 := by
    have hnat : (1806015053 : ℕ)^4607*25000000000000^3583 ≤ 2768450611237^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806015053 10000000000 2768450611237 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714844459/5000000000 : ℝ)^4607 ≤ (22800544422317/50000000000000 : ℝ)^3583 := by
    have hnat : (2714844459 : ℕ)^4607*50000000000000^3583 ≤ 22800544422317^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714844459 5000000000 22800544422317 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217731211/10000000000 : ℝ)^4607 ≤ (21662554345871/50000000000000 : ℝ)^3583 := by
    have hnat : (5217731211 : ℕ)^4607*50000000000000^3583 ≤ 21662554345871^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217731211 10000000000 21662554345871 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1806015053/10000000000 : ℝ), (2714844459/5000000000 : ℝ), (5217731211/10000000000 : ℝ)] ![(2768450611237/25000000000000 : ℝ), (22800544422317/50000000000000 : ℝ), (21662554345871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1806015053/10000000000 : ℝ)|^4607 ≤ (2768450611237/25000000000000 : ℝ)^3583
        have hw : |(-1806015053/10000000000 : ℝ)|=(1806015053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714844459/5000000000 : ℝ)|^4607 ≤ (22800544422317/50000000000000 : ℝ)^3583
        have hw : |(2714844459/5000000000 : ℝ)|=(2714844459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217731211/10000000000 : ℝ)|^4607 ≤ (21662554345871/50000000000000 : ℝ)^3583
        have hw : |(5217731211/10000000000 : ℝ)|=(5217731211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s3_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349627593/10000000000 : ℝ)*x 0 + (-7478611/39062500 : ℝ)*x 1 + (5217731203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349627593/10000000000 : ℝ)^4607 ≤ (22369179159491/50000000000000 : ℝ)^3583 := by
    have hnat : (5349627593 : ℕ)^4607*50000000000000^3583 ≤ 22369179159491^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349627593 10000000000 22369179159491 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7478611/39062500 : ℝ)^4607 ≤ (11936533058437/100000000000000 : ℝ)^3583 := by
    have hnat : (7478611 : ℕ)^4607*100000000000000^3583 ≤ 11936533058437^3583*39062500^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7478611 39062500 11936533058437 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217731203/10000000000 : ℝ)^4607 ≤ (4332510860633/10000000000000 : ℝ)^3583 := by
    have hnat : (5217731203 : ℕ)^4607*10000000000000^3583 ≤ 4332510860633^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217731203 10000000000 4332510860633 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349627593/10000000000 : ℝ), (-7478611/39062500 : ℝ), (5217731203/10000000000 : ℝ)] ![(22369179159491/50000000000000 : ℝ), (11936533058437/100000000000000 : ℝ), (4332510860633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349627593/10000000000 : ℝ)|^4607 ≤ (22369179159491/50000000000000 : ℝ)^3583
        have hw : |(5349627593/10000000000 : ℝ)|=(5349627593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7478611/39062500 : ℝ)|^4607 ≤ (11936533058437/100000000000000 : ℝ)^3583
        have hw : |(-7478611/39062500 : ℝ)|=(7478611/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217731203/10000000000 : ℝ)|^4607 ≤ (4332510860633/10000000000000 : ℝ)^3583
        have hw : |(5217731203/10000000000 : ℝ)|=(5217731203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s3_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534962763/1000000000 : ℝ)*x 0 + (2608865557/5000000000 : ℝ)*x 1 + (-478631121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534962763/1000000000 : ℝ)^4607 ≤ (22369179358421/50000000000000 : ℝ)^3583 := by
    have hnat : (534962763 : ℕ)^4607*50000000000000^3583 ≤ 22369179358421^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534962763 1000000000 22369179358421 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608865557/5000000000 : ℝ)^4607 ≤ (43325107656121/100000000000000 : ℝ)^3583 := by
    have hnat : (2608865557 : ℕ)^4607*100000000000000^3583 ≤ 43325107656121^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608865557 5000000000 43325107656121 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478631121/2500000000 : ℝ)^4607 ≤ (2984133400891/25000000000000 : ℝ)^3583 := by
    have hnat : (478631121 : ℕ)^4607*25000000000000^3583 ≤ 2984133400891^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478631121 2500000000 2984133400891 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534962763/1000000000 : ℝ), (2608865557/5000000000 : ℝ), (-478631121/2500000000 : ℝ)] ![(22369179358421/50000000000000 : ℝ), (43325107656121/100000000000000 : ℝ), (2984133400891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534962763/1000000000 : ℝ)|^4607 ≤ (22369179358421/50000000000000 : ℝ)^3583
        have hw : |(534962763/1000000000 : ℝ)|=(534962763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608865557/5000000000 : ℝ)|^4607 ≤ (43325107656121/100000000000000 : ℝ)^3583
        have hw : |(2608865557/5000000000 : ℝ)|=(2608865557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478631121/2500000000 : ℝ)|^4607 ≤ (2984133400891/25000000000000 : ℝ)^3583
        have hw : |(-478631121/2500000000 : ℝ)|=(478631121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s3_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424997069/1000000000 : ℝ)*x 0 + (2004133779/5000000000 : ℝ)*x 1 + (36027987/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424997069/1000000000 : ℝ)^4607 ≤ (8319952816121/25000000000000 : ℝ)^3583 := by
    have hnat : (424997069 : ℕ)^4607*25000000000000^3583 ≤ 8319952816121^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424997069 1000000000 8319952816121 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004133779/5000000000 : ℝ)^4607 ≤ (15433133227867/50000000000000 : ℝ)^3583 := by
    have hnat : (2004133779 : ℕ)^4607*50000000000000^3583 ≤ 15433133227867^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004133779 5000000000 15433133227867 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36027987/80000000 : ℝ)^4607 ≤ (17926961132883/50000000000000 : ℝ)^3583 := by
    have hnat : (36027987 : ℕ)^4607*50000000000000^3583 ≤ 17926961132883^3583*80000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36027987 80000000 17926961132883 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424997069/1000000000 : ℝ), (2004133779/5000000000 : ℝ), (36027987/80000000 : ℝ)] ![(8319952816121/25000000000000 : ℝ), (15433133227867/50000000000000 : ℝ), (17926961132883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424997069/1000000000 : ℝ)|^4607 ≤ (8319952816121/25000000000000 : ℝ)^3583
        have hw : |(424997069/1000000000 : ℝ)|=(424997069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2004133779/5000000000 : ℝ)|^4607 ≤ (15433133227867/50000000000000 : ℝ)^3583
        have hw : |(2004133779/5000000000 : ℝ)|=(2004133779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36027987/80000000 : ℝ)|^4607 ≤ (17926961132883/50000000000000 : ℝ)^3583
        have hw : |(36027987/80000000 : ℝ)|=(36027987/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s3_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1806044001/10000000000 : ℝ)*x 0 + (208754063/400000000 : ℝ)*x 1 + (542856003/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806044001/10000000000 : ℝ)^4607 ≤ (2768507667901/25000000000000 : ℝ)^3583 := by
    have hnat : (1806044001 : ℕ)^4607*25000000000000^3583 ≤ 2768507667901^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806044001 10000000000 2768507667901 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208754063/400000000 : ℝ)^4607 ≤ (43337070637597/100000000000000 : ℝ)^3583 := by
    have hnat : (208754063 : ℕ)^4607*100000000000000^3583 ≤ 43337070637597^3583*400000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208754063 400000000 43337070637597 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542856003/1000000000 : ℝ)^4607 ≤ (45588898678587/100000000000000 : ℝ)^3583 := by
    have hnat : (542856003 : ℕ)^4607*100000000000000^3583 ≤ 45588898678587^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542856003 1000000000 45588898678587 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1806044001/10000000000 : ℝ), (208754063/400000000 : ℝ), (542856003/1000000000 : ℝ)] ![(2768507667901/25000000000000 : ℝ), (43337070637597/100000000000000 : ℝ), (45588898678587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1806044001/10000000000 : ℝ)|^4607 ≤ (2768507667901/25000000000000 : ℝ)^3583
        have hw : |(-1806044001/10000000000 : ℝ)|=(1806044001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208754063/400000000 : ℝ)|^4607 ≤ (43337070637597/100000000000000 : ℝ)^3583
        have hw : |(208754063/400000000 : ℝ)|=(208754063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542856003/1000000000 : ℝ)|^4607 ≤ (45588898678587/100000000000000 : ℝ)^3583
        have hw : |(542856003/1000000000 : ℝ)|=(542856003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s3_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646826411/5000000000 : ℝ)*x 0 + (-170369551/1000000000 : ℝ)*x 1 + (1085711991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646826411/5000000000 : ℝ)^4607 ≤ (44137366218517/100000000000000 : ℝ)^3583 := by
    have hnat : (2646826411 : ℕ)^4607*100000000000000^3583 ≤ 44137366218517^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646826411 5000000000 44137366218517 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170369551/1000000000 : ℝ)^4607 ≤ (10273735890709/100000000000000 : ℝ)^3583 := by
    have hnat : (170369551 : ℕ)^4607*100000000000000^3583 ≤ 10273735890709^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170369551 1000000000 10273735890709 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085711991/2000000000 : ℝ)^4607 ≤ (11397224467183/25000000000000 : ℝ)^3583 := by
    have hnat : (1085711991 : ℕ)^4607*25000000000000^3583 ≤ 11397224467183^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085711991 2000000000 11397224467183 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646826411/5000000000 : ℝ), (-170369551/1000000000 : ℝ), (1085711991/2000000000 : ℝ)] ![(44137366218517/100000000000000 : ℝ), (10273735890709/100000000000000 : ℝ), (11397224467183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646826411/5000000000 : ℝ)|^4607 ≤ (44137366218517/100000000000000 : ℝ)^3583
        have hw : |(2646826411/5000000000 : ℝ)|=(2646826411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170369551/1000000000 : ℝ)|^4607 ≤ (10273735890709/100000000000000 : ℝ)^3583
        have hw : |(-170369551/1000000000 : ℝ)|=(170369551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085711991/2000000000 : ℝ)|^4607 ≤ (11397224467183/25000000000000 : ℝ)^3583
        have hw : |(1085711991/2000000000 : ℝ)|=(1085711991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s3_6 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264682631/500000000 : ℝ)*x 0 + (5428560079/10000000000 : ℝ)*x 1 + (-1703695617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264682631/500000000 : ℝ)^4607 ≤ (2206868202647/5000000000000 : ℝ)^3583 := by
    have hnat : (264682631 : ℕ)^4607*5000000000000^3583 ≤ 2206868202647^3583*500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264682631 500000000 2206868202647 5000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428560079/10000000000 : ℝ)^4607 ≤ (11397224801923/25000000000000 : ℝ)^3583 := by
    have hnat : (5428560079 : ℕ)^4607*25000000000000^3583 ≤ 11397224801923^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428560079 10000000000 11397224801923 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1703695617/10000000000 : ℝ)^4607 ≤ (10273736720353/100000000000000 : ℝ)^3583 := by
    have hnat : (1703695617 : ℕ)^4607*100000000000000^3583 ≤ 10273736720353^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703695617 10000000000 10273736720353 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264682631/500000000 : ℝ), (5428560079/10000000000 : ℝ), (-1703695617/10000000000 : ℝ)] ![(2206868202647/5000000000000 : ℝ), (11397224801923/25000000000000 : ℝ), (10273736720353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264682631/500000000 : ℝ)|^4607 ≤ (2206868202647/5000000000000 : ℝ)^3583
        have hw : |(264682631/500000000 : ℝ)|=(264682631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428560079/10000000000 : ℝ)|^4607 ≤ (11397224801923/25000000000000 : ℝ)^3583
        have hw : |(5428560079/10000000000 : ℝ)|=(5428560079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1703695617/10000000000 : ℝ)|^4607 ≤ (10273736720353/100000000000000 : ℝ)^3583
        have hw : |(-1703695617/10000000000 : ℝ)|=(1703695617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s3_7 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212501903/500000000 : ℝ)*x 0 + (900176079/2000000000 : ℝ)*x 1 + (1002726297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212501903/500000000 : ℝ)^4607 ≤ (16640244791643/50000000000000 : ℝ)^3583 := by
    have hnat : (212501903 : ℕ)^4607*50000000000000^3583 ≤ 16640244791643^3583*500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212501903 500000000 16640244791643 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900176079/2000000000 : ℝ)^4607 ≤ (7165425026849/20000000000000 : ℝ)^3583 := by
    have hnat : (900176079 : ℕ)^4607*20000000000000^3583 ≤ 7165425026849^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900176079 2000000000 7165425026849 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002726297/2500000000 : ℝ)^4607 ≤ (30892385272873/100000000000000 : ℝ)^3583 := by
    have hnat : (1002726297 : ℕ)^4607*100000000000000^3583 ≤ 30892385272873^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002726297 2500000000 30892385272873 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212501903/500000000 : ℝ), (900176079/2000000000 : ℝ), (1002726297/2500000000 : ℝ)] ![(16640244791643/50000000000000 : ℝ), (7165425026849/20000000000000 : ℝ), (30892385272873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212501903/500000000 : ℝ)|^4607 ≤ (16640244791643/50000000000000 : ℝ)^3583
        have hw : |(212501903/500000000 : ℝ)|=(212501903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900176079/2000000000 : ℝ)|^4607 ≤ (7165425026849/20000000000000 : ℝ)^3583
        have hw : |(900176079/2000000000 : ℝ)|=(900176079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002726297/2500000000 : ℝ)|^4607 ≤ (30892385272873/100000000000000 : ℝ)^3583
        have hw : |(1002726297/2500000000 : ℝ)|=(1002726297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11033/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15527/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2683/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2683/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2683/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2683/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2683/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2683/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2683/25000 : ℝ) ^ (4605/1024 : ℝ) ≤ (4374241844120627/100000000000000000000 : ℝ) := by
    have hpowers : (2683/25000 : ℝ)^4605 ≤ (4374241844120627/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2683 : ℕ)^4605*100000000000000000000^1024 ≤ 4374241844120627^1024*25000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2683 25000 4374241844120627 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2683/25000 : ℝ)) (X := (4374241844120627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15853/100000 : ℝ) ^ (4605/1024 : ℝ) ≤ (632098850343851/2500000000000000000 : ℝ) := by
    have hpowers : (15853/100000 : ℝ)^4605 ≤ (632098850343851/2500000000000000000 : ℝ)^1024 := by
      have hnat : (15853 : ℕ)^4605*2500000000000000000^1024 ≤ 632098850343851^1024*100000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15853 100000 632098850343851 2500000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15853/100000 : ℝ)) (X := (632098850343851/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004374241844120627/50000000000000000000 : ℝ) ≤ (2500048632695907/2500000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50004374241844120627/50000000000000000000 : ℝ)^1024 ≤ (2500048632695907/2500000000000000 : ℝ)^4605 := by
      have hnat : (50004374241844120627 : ℕ)^1024*2500000000000000^4605 ≤ 2500048632695907^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004374241844120627 50000000000000000000 2500048632695907 2500000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500048632695907/2500000000000000 : ℝ)) (X := (50004374241844120627/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029658195857874667/100000000000000000000 : ℝ) ≤ (5000329712171867/5000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (100029658195857874667/100000000000000000000 : ℝ)^1024 ≤ (5000329712171867/5000000000000000 : ℝ)^4605 := by
      have hnat : (100029658195857874667 : ℕ)^1024*5000000000000000^4605 ≤ 5000329712171867^4605*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029658195857874667 100000000000000000000 5000329712171867 5000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000329712171867/5000000000000000 : ℝ)) (X := (100029658195857874667/100000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250632098850343851/1250000000000000000 : ℝ) ≤ (62507026986899/62500000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (1250632098850343851/1250000000000000000 : ℝ)^1024 ≤ (62507026986899/62500000000000 : ℝ)^4605 := by
      have hnat : (1250632098850343851 : ℕ)^1024*62500000000000^4605 ≤ 62507026986899^4605*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250632098850343851 1250000000000000000 62507026986899 62500000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62507026986899/62500000000000 : ℝ)) (X := (1250632098850343851/1250000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4374241844120627/100000000000000000000 : ℝ) ≤ ((12800254429192210951/12802500000000000000 : ℝ)+2*(232446780053/256050000000000 : ℝ)*(2683/25000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (12800254429192210951/12802500000000000000 : ℝ)+2*(232446780053/256050000000000 : ℝ)*(2683/25000 : ℝ)=(2500048632695907/2500000000000000 : ℝ) by norm_num, show 1+2*(4374241844120627/100000000000000000000 : ℝ)=(50004374241844120627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(632098850343851/2500000000000000000 : ℝ)+(4374241844120627/100000000000000000000 : ℝ) ≤ ((12800254429192210951/12802500000000000000 : ℝ)+(232446780053/256050000000000 : ℝ)*((15853/100000 : ℝ)+(2683/25000 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (12800254429192210951/12802500000000000000 : ℝ)+(232446780053/256050000000000 : ℝ)*((15853/100000 : ℝ)+(2683/25000 : ℝ))=(5000329712171867/5000000000000000 : ℝ) by norm_num, show 1+(632098850343851/2500000000000000000 : ℝ)+(4374241844120627/100000000000000000000 : ℝ)=(100029658195857874667/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(632098850343851/2500000000000000000 : ℝ) ≤ ((12800254429192210951/12802500000000000000 : ℝ)+2*(232446780053/256050000000000 : ℝ)*(15853/100000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (12800254429192210951/12802500000000000000 : ℝ)+2*(232446780053/256050000000000 : ℝ)*(15853/100000 : ℝ)=(62507026986899/62500000000000 : ℝ) by norm_num, show 1+2*(632098850343851/2500000000000000000 : ℝ)=(1250632098850343851/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12800254429192210951/12802500000000000000 : ℝ)*(X 1 0+X 2 0)+(232446780053/256050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (2683/25000 : ℝ)) (hi := (15853/100000 : ℝ)) (c := (12800254429192210951/12802500000000000000 : ℝ)) (alpha := (232446780053/256050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12800254429192210951/12802500000000000000 : ℝ)*(X 0 1+X 2 1)+(232446780053/256050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (2683/25000 : ℝ)) (hi := (15853/100000 : ℝ)) (c := (12800254429192210951/12802500000000000000 : ℝ)) (alpha := (232446780053/256050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12800254429192210951/12802500000000000000 : ℝ)*(X 0 2+X 1 2)+(232446780053/256050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (2683/25000 : ℝ)) (hi := (15853/100000 : ℝ)) (c := (12800254429192210951/12802500000000000000 : ℝ)) (alpha := (232446780053/256050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1806015053/10000000000 : ℝ)*X 0 0+(2714844459/5000000000 : ℝ)*X 0 1+(5217731211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349627593/10000000000 : ℝ)*X 1 0+(-7478611/39062500 : ℝ)*X 1 1+(5217731203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534962763/1000000000 : ℝ)*X 2 0+(2608865557/5000000000 : ℝ)*X 2 1+(-478631121/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((424997069/1000000000 : ℝ)*X 0 0+(2004133779/5000000000 : ℝ)*X 0 1+(36027987/80000000 : ℝ)*X 0 2+(424997069/1000000000 : ℝ)*X 1 0+(2004133779/5000000000 : ℝ)*X 1 1+(36027987/80000000 : ℝ)*X 1 2+(424997069/1000000000 : ℝ)*X 2 0+(2004133779/5000000000 : ℝ)*X 2 1+(36027987/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1806044001/10000000000 : ℝ)*X 0 0+(208754063/400000000 : ℝ)*X 0 1+(542856003/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646826411/5000000000 : ℝ)*X 1 0+(-170369551/1000000000 : ℝ)*X 1 1+(1085711991/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264682631/500000000 : ℝ)*X 2 0+(5428560079/10000000000 : ℝ)*X 2 1+(-1703695617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((212501903/500000000 : ℝ)*X 0 0+(900176079/2000000000 : ℝ)*X 0 1+(1002726297/2500000000 : ℝ)*X 0 2+(212501903/500000000 : ℝ)*X 1 0+(900176079/2000000000 : ℝ)*X 1 1+(1002726297/2500000000 : ℝ)*X 1 2+(212501903/500000000 : ℝ)*X 2 0+(900176079/2000000000 : ℝ)*X 2 1+(1002726297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201706045194892658376340147/21337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151155997/10000000000000 : ℝ)*(base19) + (1357417757/100000000000000 : ℝ)*(base23) + (99916823/100000000000000 : ℝ)*(lower2) + (10646973/4000000000000 : ℝ)*(upper3) + (34108667/50000000000000 : ℝ)*(upper5) + (336862523452003/10000000000000 : ℝ)*(major0) + (336862523452003/10000000000000 : ℝ)*(major1) + (336862523452003/10000000000000 : ℝ)*(major2) + (589743433846801/12500000000000 : ℝ)*(sp0) + (589745930255197/12500000000000 : ℝ)*(sp1) + (4717967596183789/100000000000000 : ℝ)*(sp2) + (1009634691639863/50000000000000 : ℝ)*(sp3) + (10741413569/50000000000000 : ℝ)*(sp4) + (369282957/3125000000000 : ℝ)*(sp7) + (40385624006687/2000000000000 : ℝ)*(f.failure) + (2358984476800773/50000000000000 : ℝ)*(f.sum) + (15429308011429/2560500000000000000000000000 : ℝ)*base65 + (629876190949384853/128025000000000000000000000000000 : ℝ)*base67 + (371099857432315147/128025000000000000000000000000000 : ℝ)*base70 + (1513037646089734853/128025000000000000000000000000000 : ℝ)*base71 + (3933278887753/640125000000000000000000000 : ℝ)*base73 + (807761599874815147/128025000000000000000000000000000 : ℝ)*base76 + (620743915746184853/128025000000000000000000000000000 : ℝ)*base77 + (1023161558842084853/128025000000000000000000000000000 : ℝ)*base79 + (1888629634763/512100000000000000000000000 : ℝ)*base81 + (669811/50000000000000000000 : ℝ)*base90 + (669811/50000000000000000000 : ℝ)*base92 + (669811/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (447071491791232281633411909/35562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2188350093/100000000000000 : ℝ)*(base19) + (2111556719/100000000000000 : ℝ)*(base23) + (253918237/100000000000000 : ℝ)*(upper3) + (64878443/100000000000000 : ℝ)*(lower4) + (280430477/100000000000000 : ℝ)*(upper5) + (1702360571455077/50000000000000 : ℝ)*(major0) + (1702360571455077/50000000000000 : ℝ)*(major1) + (1702360571455077/50000000000000 : ℝ)*(major2) + (33710248507/100000000000000 : ℝ)*(sp1) + (1603271579/5000000000000 : ℝ)*(sp2) + (1192130853896903/25000000000000 : ℝ)*(sp4) + (4768487516989011/100000000000000 : ℝ)*(sp5) + (2384244619299657/50000000000000 : ℝ)*(sp6) + (204091845118501/10000000000000 : ℝ)*(sp7) + (204091845118501/10000000000000 : ℝ)*(f.failure) + (1192130853896903/25000000000000 : ℝ)*(f.sum) + (3416439924941/1066875000000000000000000000 : ℝ)*base65 + (1038232693907750591/213375000000000000000000000000000 : ℝ)*base68 + (465366137624000591/213375000000000000000000000000000 : ℝ)*base70 + (623658669692124409/213375000000000000000000000000000 : ℝ)*base71 + (1027688391617/533437500000000000000000000 : ℝ)*base74 + (882871524543249409/213375000000000000000000000000000 : ℝ)*base75 + (1717377757259000591/213375000000000000000000000000000 : ℝ)*base78 + (3646673154330500591/213375000000000000000000000000000 : ℝ)*base80 + (7159876864831/4267500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (2725247/250000000000000000000 : ℝ)*base89 + (2725247/250000000000000000000 : ℝ)*base91 + (2725247/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1555_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1555_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1555_s4_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1806281907/10000000000 : ℝ)*x 0 + (2713952687/5000000000 : ℝ)*x 1 + (163104311/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806281907/10000000000 : ℝ)^4607 ≤ (2768976591811/25000000000000 : ℝ)^3583 := by
    have hnat : (1806281907 : ℕ)^4607*25000000000000^3583 ≤ 2768976591811^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806281907 10000000000 2768976591811 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713952687/5000000000 : ℝ)^4607 ≤ (364654638269/800000000000 : ℝ)^3583 := by
    have hnat : (2713952687 : ℕ)^4607*800000000000^3583 ≤ 364654638269^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713952687 5000000000 364654638269 800000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163104311/312500000 : ℝ)^4607 ≤ (10835565958727/25000000000000 : ℝ)^3583 := by
    have hnat : (163104311 : ℕ)^4607*25000000000000^3583 ≤ 10835565958727^3583*312500000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163104311 312500000 10835565958727 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1806281907/10000000000 : ℝ), (2713952687/5000000000 : ℝ), (163104311/312500000 : ℝ)] ![(2768976591811/25000000000000 : ℝ), (364654638269/800000000000 : ℝ), (10835565958727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1806281907/10000000000 : ℝ)|^4607 ≤ (2768976591811/25000000000000 : ℝ)^3583
        have hw : |(-1806281907/10000000000 : ℝ)|=(1806281907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713952687/5000000000 : ℝ)|^4607 ≤ (364654638269/800000000000 : ℝ)^3583
        have hw : |(2713952687/5000000000 : ℝ)|=(2713952687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163104311/312500000 : ℝ)|^4607 ≤ (10835565958727/25000000000000 : ℝ)^3583
        have hw : |(163104311/312500000 : ℝ)|=(163104311/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s4_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534915683/1000000000 : ℝ)*x 0 + (-478253681/2500000000 : ℝ)*x 1 + (5219338701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534915683/1000000000 : ℝ)^4607 ≤ (44733296288479/100000000000000 : ℝ)^3583 := by
    have hnat : (534915683 : ℕ)^4607*100000000000000^3583 ≤ 44733296288479^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534915683 1000000000 44733296288479 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478253681/2500000000 : ℝ)^4607 ≤ (11924431867737/100000000000000 : ℝ)^3583 := by
    have hnat : (478253681 : ℕ)^4607*100000000000000^3583 ≤ 11924431867737^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478253681 2500000000 11924431867737 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219338701/10000000000 : ℝ)^4607 ≤ (43342271832319/100000000000000 : ℝ)^3583 := by
    have hnat : (5219338701 : ℕ)^4607*100000000000000^3583 ≤ 43342271832319^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219338701 10000000000 43342271832319 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534915683/1000000000 : ℝ), (-478253681/2500000000 : ℝ), (5219338701/10000000000 : ℝ)] ![(44733296288479/100000000000000 : ℝ), (11924431867737/100000000000000 : ℝ), (43342271832319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534915683/1000000000 : ℝ)|^4607 ≤ (44733296288479/100000000000000 : ℝ)^3583
        have hw : |(534915683/1000000000 : ℝ)|=(534915683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478253681/2500000000 : ℝ)|^4607 ≤ (11924431867737/100000000000000 : ℝ)^3583
        have hw : |(-478253681/2500000000 : ℝ)|=(478253681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219338701/10000000000 : ℝ)|^4607 ≤ (43342271832319/100000000000000 : ℝ)^3583
        have hw : |(5219338701/10000000000 : ℝ)|=(5219338701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s4_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349156471/10000000000 : ℝ)*x 0 + (1304834719/2500000000 : ℝ)*x 1 + (-478253743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349156471/10000000000 : ℝ)^4607 ≤ (8946658485653/20000000000000 : ℝ)^3583 := by
    have hnat : (5349156471 : ℕ)^4607*20000000000000^3583 ≤ 8946658485653^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349156471 10000000000 8946658485653 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304834719/2500000000 : ℝ)^4607 ≤ (43342273700873/100000000000000 : ℝ)^3583 := by
    have hnat : (1304834719 : ℕ)^4607*100000000000000^3583 ≤ 43342273700873^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304834719 2500000000 43342273700873 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478253743/2500000000 : ℝ)^4607 ≤ (5962216927699/50000000000000 : ℝ)^3583 := by
    have hnat : (478253743 : ℕ)^4607*50000000000000^3583 ≤ 5962216927699^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478253743 2500000000 5962216927699 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349156471/10000000000 : ℝ), (1304834719/2500000000 : ℝ), (-478253743/2500000000 : ℝ)] ![(8946658485653/20000000000000 : ℝ), (43342273700873/100000000000000 : ℝ), (5962216927699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349156471/10000000000 : ℝ)|^4607 ≤ (8946658485653/20000000000000 : ℝ)^3583
        have hw : |(5349156471/10000000000 : ℝ)|=(5349156471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304834719/2500000000 : ℝ)|^4607 ≤ (43342273700873/100000000000000 : ℝ)^3583
        have hw : |(1304834719/2500000000 : ℝ)|=(1304834719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478253743/2500000000 : ℝ)|^4607 ≤ (5962216927699/50000000000000 : ℝ)^3583
        have hw : |(-478253743/2500000000 : ℝ)|=(478253743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s4_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125069653/5000000000 : ℝ)*x 0 + (2006105503/5000000000 : ℝ)*x 1 + (449951717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125069653/5000000000 : ℝ)^4607 ≤ (16640754495181/50000000000000 : ℝ)^3583 := by
    have hnat : (2125069653 : ℕ)^4607*50000000000000^3583 ≤ 16640754495181^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125069653 5000000000 16640754495181 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006105503/5000000000 : ℝ)^4607 ≤ (6181063559439/20000000000000 : ℝ)^3583 := by
    have hnat : (2006105503 : ℕ)^4607*20000000000000^3583 ≤ 6181063559439^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006105503 5000000000 6181063559439 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449951717/1000000000 : ℝ)^4607 ≤ (8953293298271/25000000000000 : ℝ)^3583 := by
    have hnat : (449951717 : ℕ)^4607*25000000000000^3583 ≤ 8953293298271^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449951717 1000000000 8953293298271 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125069653/5000000000 : ℝ), (2006105503/5000000000 : ℝ), (449951717/1000000000 : ℝ)] ![(16640754495181/50000000000000 : ℝ), (6181063559439/20000000000000 : ℝ), (8953293298271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125069653/5000000000 : ℝ)|^4607 ≤ (16640754495181/50000000000000 : ℝ)^3583
        have hw : |(2125069653/5000000000 : ℝ)|=(2125069653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006105503/5000000000 : ℝ)|^4607 ≤ (6181063559439/20000000000000 : ℝ)^3583
        have hw : |(2006105503/5000000000 : ℝ)|=(2006105503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449951717/1000000000 : ℝ)|^4607 ≤ (8953293298271/25000000000000 : ℝ)^3583
        have hw : |(449951717/1000000000 : ℝ)|=(449951717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s4_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1806308881/10000000000 : ℝ)*x 0 + (5220423741/10000000000 : ℝ)*x 1 + (5426811917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806308881/10000000000 : ℝ)^4607 ≤ (11076119039789/100000000000000 : ℝ)^3583 := by
    have hnat : (1806308881 : ℕ)^4607*100000000000000^3583 ≤ 11076119039789^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806308881 10000000000 11076119039789 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220423741/10000000000 : ℝ)^4607 ≤ (1354808051191/3125000000000 : ℝ)^3583 := by
    have hnat : (5220423741 : ℕ)^4607*3125000000000^3583 ≤ 1354808051191^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220423741 10000000000 1354808051191 3125000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426811917/10000000000 : ℝ)^4607 ≤ (45570023312817/100000000000000 : ℝ)^3583 := by
    have hnat : (5426811917 : ℕ)^4607*100000000000000^3583 ≤ 45570023312817^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426811917 10000000000 45570023312817 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1806308881/10000000000 : ℝ), (5220423741/10000000000 : ℝ), (5426811917/10000000000 : ℝ)] ![(11076119039789/100000000000000 : ℝ), (1354808051191/3125000000000 : ℝ), (45570023312817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1806308881/10000000000 : ℝ)|^4607 ≤ (11076119039789/100000000000000 : ℝ)^3583
        have hw : |(-1806308881/10000000000 : ℝ)|=(1806308881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220423741/10000000000 : ℝ)|^4607 ≤ (1354808051191/3125000000000 : ℝ)^3583
        have hw : |(5220423741/10000000000 : ℝ)|=(5220423741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426811917/10000000000 : ℝ)|^4607 ≤ (45570023312817/100000000000000 : ℝ)^3583
        have hw : |(5426811917/10000000000 : ℝ)|=(5426811917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s4_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294077957/10000000000 : ℝ)*x 0 + (-852770797/5000000000 : ℝ)*x 1 + (2713405987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294077957/10000000000 : ℝ)^4607 ≤ (44141924007429/100000000000000 : ℝ)^3583 := by
    have hnat : (5294077957 : ℕ)^4607*100000000000000^3583 ≤ 44141924007429^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294077957 10000000000 44141924007429 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852770797/5000000000 : ℝ)^4607 ≤ (1028805204941/10000000000000 : ℝ)^3583 := by
    have hnat : (852770797 : ℕ)^4607*10000000000000^3583 ≤ 1028805204941^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852770797 5000000000 1028805204941 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713405987/5000000000 : ℝ)^4607 ≤ (182280095713/400000000000 : ℝ)^3583 := by
    have hnat : (2713405987 : ℕ)^4607*400000000000^3583 ≤ 182280095713^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713405987 5000000000 182280095713 400000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294077957/10000000000 : ℝ), (-852770797/5000000000 : ℝ), (2713405987/5000000000 : ℝ)] ![(44141924007429/100000000000000 : ℝ), (1028805204941/10000000000000 : ℝ), (182280095713/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294077957/10000000000 : ℝ)|^4607 ≤ (44141924007429/100000000000000 : ℝ)^3583
        have hw : |(5294077957/10000000000 : ℝ)|=(5294077957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852770797/5000000000 : ℝ)|^4607 ≤ (1028805204941/10000000000000 : ℝ)^3583
        have hw : |(-852770797/5000000000 : ℝ)|=(852770797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713405987/5000000000 : ℝ)|^4607 ≤ (182280095713/400000000000 : ℝ)^3583
        have hw : |(2713405987/5000000000 : ℝ)|=(2713405987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s4_6 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647038987/5000000000 : ℝ)*x 0 + (678351501/1250000000 : ℝ)*x 1 + (-1705541523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647038987/5000000000 : ℝ)^4607 ≤ (8828384837937/20000000000000 : ℝ)^3583 := by
    have hnat : (2647038987 : ℕ)^4607*20000000000000^3583 ≤ 8828384837937^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647038987 5000000000 8828384837937 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678351501/1250000000 : ℝ)^4607 ≤ (911400485907/2000000000000 : ℝ)^3583 := by
    have hnat : (678351501 : ℕ)^4607*2000000000000^3583 ≤ 911400485907^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678351501 1250000000 911400485907 2000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1705541523/10000000000 : ℝ)^4607 ≤ (1286006437341/12500000000000 : ℝ)^3583 := by
    have hnat : (1705541523 : ℕ)^4607*12500000000000^3583 ≤ 1286006437341^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705541523 10000000000 1286006437341 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647038987/5000000000 : ℝ), (678351501/1250000000 : ℝ), (-1705541523/10000000000 : ℝ)] ![(8828384837937/20000000000000 : ℝ), (911400485907/2000000000000 : ℝ), (1286006437341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647038987/5000000000 : ℝ)|^4607 ≤ (8828384837937/20000000000000 : ℝ)^3583
        have hw : |(2647038987/5000000000 : ℝ)|=(2647038987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678351501/1250000000 : ℝ)|^4607 ≤ (911400485907/2000000000000 : ℝ)^3583
        have hw : |(678351501/1250000000 : ℝ)|=(678351501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1705541523/10000000000 : ℝ)|^4607 ≤ (1286006437341/12500000000000 : ℝ)^3583
        have hw : |(-1705541523/10000000000 : ℝ)|=(1705541523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s4_7 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250203503/10000000000 : ℝ)*x 0 + (4496982329/10000000000 : ℝ)*x 1 + (4014764557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250203503/10000000000 : ℝ)^4607 ≤ (33282155368887/100000000000000 : ℝ)^3583 := by
    have hnat : (4250203503 : ℕ)^4607*100000000000000^3583 ≤ 33282155368887^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250203503 10000000000 33282155368887 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496982329/10000000000 : ℝ)^4607 ≤ (17893616773423/50000000000000 : ℝ)^3583 := by
    have hnat : (4496982329 : ℕ)^4607*50000000000000^3583 ≤ 17893616773423^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496982329 10000000000 17893616773423 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4014764557/10000000000 : ℝ)^4607 ≤ (30930611061289/100000000000000 : ℝ)^3583 := by
    have hnat : (4014764557 : ℕ)^4607*100000000000000^3583 ≤ 30930611061289^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014764557 10000000000 30930611061289 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250203503/10000000000 : ℝ), (4496982329/10000000000 : ℝ), (4014764557/10000000000 : ℝ)] ![(33282155368887/100000000000000 : ℝ), (17893616773423/50000000000000 : ℝ), (30930611061289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250203503/10000000000 : ℝ)|^4607 ≤ (33282155368887/100000000000000 : ℝ)^3583
        have hw : |(4250203503/10000000000 : ℝ)|=(4250203503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496982329/10000000000 : ℝ)|^4607 ≤ (17893616773423/50000000000000 : ℝ)^3583
        have hw : |(4496982329/10000000000 : ℝ)|=(4496982329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4014764557/10000000000 : ℝ)|^4607 ≤ (30930611061289/100000000000000 : ℝ)^3583
        have hw : |(4014764557/10000000000 : ℝ)|=(4014764557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2767/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11033/100000 : ℝ) ^ (4605/1024 : ℝ) ≤ (1238414131301269/25000000000000000000 : ℝ) := by
    have hpowers : (11033/100000 : ℝ)^4605 ≤ (1238414131301269/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11033 : ℕ)^4605*25000000000000000000^1024 ≤ 1238414131301269^1024*100000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11033 100000 1238414131301269 25000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11033/100000 : ℝ)) (X := (1238414131301269/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15527/100000 : ℝ) ^ (4605/1024 : ℝ) ≤ (23028404492459603/100000000000000000000 : ℝ) := by
    have hpowers : (15527/100000 : ℝ)^4605 ≤ (23028404492459603/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15527 : ℕ)^4605*100000000000000000000^1024 ≤ 23028404492459603^1024*100000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15527 100000 23028404492459603 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15527/100000 : ℝ)) (X := (23028404492459603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501238414131301269/12500000000000000000 : ℝ) ≤ (10000220297454613/10000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (12501238414131301269/12500000000000000000 : ℝ)^1024 ≤ (10000220297454613/10000000000000000 : ℝ)^4605 := by
      have hnat : (12501238414131301269 : ℕ)^1024*10000000000000000^4605 ≤ 10000220297454613^4605*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501238414131301269 12500000000000000000 10000220297454613 10000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000220297454613/10000000000000000 : ℝ)) (X := (12501238414131301269/12500000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027982061017664679/100000000000000000000 : ℝ) ≤ (10000622160988409/10000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (100027982061017664679/100000000000000000000 : ℝ)^1024 ≤ (10000622160988409/10000000000000000 : ℝ)^4605 := by
      have hnat : (100027982061017664679 : ℕ)^1024*10000000000000000^4605 ≤ 10000622160988409^4605*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027982061017664679 100000000000000000000 10000622160988409 10000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000622160988409/10000000000000000 : ℝ)) (X := (100027982061017664679/100000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023028404492459603/50000000000000000000 : ℝ) ≤ (2000204804904441/2000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50023028404492459603/50000000000000000000 : ℝ)^1024 ≤ (2000204804904441/2000000000000000 : ℝ)^4605 := by
      have hnat : (50023028404492459603 : ℕ)^1024*2000000000000000^4605 ≤ 2000204804904441^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023028404492459603 50000000000000000000 2000204804904441 2000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000204804904441/2000000000000000 : ℝ)) (X := (50023028404492459603/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1238414131301269/25000000000000000000 : ℝ) ≤ ((22466061248012144143/22470000000000000000 : ℝ)+2*(100465883449/112350000000000 : ℝ)*(11033/100000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (22466061248012144143/22470000000000000000 : ℝ)+2*(100465883449/112350000000000 : ℝ)*(11033/100000 : ℝ)=(10000220297454613/10000000000000000 : ℝ) by norm_num, show 1+2*(1238414131301269/25000000000000000000 : ℝ)=(12501238414131301269/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23028404492459603/100000000000000000000 : ℝ)+(1238414131301269/25000000000000000000 : ℝ) ≤ ((22466061248012144143/22470000000000000000 : ℝ)+(100465883449/112350000000000 : ℝ)*((15527/100000 : ℝ)+(11033/100000 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (22466061248012144143/22470000000000000000 : ℝ)+(100465883449/112350000000000 : ℝ)*((15527/100000 : ℝ)+(11033/100000 : ℝ))=(10000622160988409/10000000000000000 : ℝ) by norm_num, show 1+(23028404492459603/100000000000000000000 : ℝ)+(1238414131301269/25000000000000000000 : ℝ)=(100027982061017664679/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23028404492459603/100000000000000000000 : ℝ) ≤ ((22466061248012144143/22470000000000000000 : ℝ)+2*(100465883449/112350000000000 : ℝ)*(15527/100000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (22466061248012144143/22470000000000000000 : ℝ)+2*(100465883449/112350000000000 : ℝ)*(15527/100000 : ℝ)=(2000204804904441/2000000000000000 : ℝ) by norm_num, show 1+2*(23028404492459603/100000000000000000000 : ℝ)=(50023028404492459603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22466061248012144143/22470000000000000000 : ℝ)*(X 1 0+X 2 0)+(100465883449/112350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (22466061248012144143/22470000000000000000 : ℝ)) (alpha := (100465883449/112350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22466061248012144143/22470000000000000000 : ℝ)*(X 0 1+X 2 1)+(100465883449/112350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (22466061248012144143/22470000000000000000 : ℝ)) (alpha := (100465883449/112350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22466061248012144143/22470000000000000000 : ℝ)*(X 0 2+X 1 2)+(100465883449/112350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (22466061248012144143/22470000000000000000 : ℝ)) (alpha := (100465883449/112350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1806281907/10000000000 : ℝ)*X 0 0+(2713952687/5000000000 : ℝ)*X 0 1+(163104311/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534915683/1000000000 : ℝ)*X 1 0+(-478253681/2500000000 : ℝ)*X 1 1+(5219338701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349156471/10000000000 : ℝ)*X 2 0+(1304834719/2500000000 : ℝ)*X 2 1+(-478253743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125069653/5000000000 : ℝ)*X 0 0+(2006105503/5000000000 : ℝ)*X 0 1+(449951717/1000000000 : ℝ)*X 0 2+(2125069653/5000000000 : ℝ)*X 1 0+(2006105503/5000000000 : ℝ)*X 1 1+(449951717/1000000000 : ℝ)*X 1 2+(2125069653/5000000000 : ℝ)*X 2 0+(2006105503/5000000000 : ℝ)*X 2 1+(449951717/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1806308881/10000000000 : ℝ)*X 0 0+(5220423741/10000000000 : ℝ)*X 0 1+(5426811917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294077957/10000000000 : ℝ)*X 1 0+(-852770797/5000000000 : ℝ)*X 1 1+(2713405987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647038987/5000000000 : ℝ)*X 2 0+(678351501/1250000000 : ℝ)*X 2 1+(-1705541523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250203503/10000000000 : ℝ)*X 0 0+(4496982329/10000000000 : ℝ)*X 0 1+(4014764557/10000000000 : ℝ)*X 0 2+(4250203503/10000000000 : ℝ)*X 1 0+(4496982329/10000000000 : ℝ)*X 1 1+(4014764557/10000000000 : ℝ)*X 1 2+(4250203503/10000000000 : ℝ)*X 2 0+(4496982329/10000000000 : ℝ)*X 2 1+(4014764557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127209921665253394615810499/46812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (864803401/100000000000000 : ℝ)*(base19) + (245330377/50000000000000 : ℝ)*(base23) + (86023723/100000000000000 : ℝ)*(upper2) + (16637949/5000000000000 : ℝ)*(upper3) + (114029993/100000000000000 : ℝ)*(upper4) + (855846712036493/25000000000000 : ℝ)*(major0) + (855846712036493/25000000000000 : ℝ)*(major1) + (855846712036493/25000000000000 : ℝ)*(major2) + (958929005641429/20000000000000 : ℝ)*(sp0) + (239733268049521/5000000000000 : ℝ)*(sp1) + (1198666433783267/25000000000000 : ℝ)*(sp2) + (2052101193173647/100000000000000 : ℝ)*(sp3) + (21197586677/100000000000000 : ℝ)*(sp4) + (3093371653/50000000000000 : ℝ)*(sp7) + (2052107379916953/100000000000000 : ℝ)*(f.failure) + (4794666225793821/100000000000000 : ℝ)*(f.sum) + (5977073927269/2808750000000000000000000000 : ℝ)*base65 + (1120724682497213167/187250000000000000000000000000000 : ℝ)*base68 + (1330543332912713167/187250000000000000000000000000000 : ℝ)*base70 + (526457607170463167/187250000000000000000000000000000 : ℝ)*base72 + (7486917850751/2808750000000000000000000000 : ℝ)*base74 + (168178034417536833/187250000000000000000000000000000 : ℝ)*base75 + (906708883813463167/187250000000000000000000000000000 : ℝ)*base78 + (446391683764463167/187250000000000000000000000000000 : ℝ)*base80 + (8148808961263/1404375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (22828891/2500000000000000000000 : ℝ)*base89 + (22828891/2500000000000000000000 : ℝ)*base91 + (22828891/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (993576003740119419731549819/187250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (631399221/100000000000000 : ℝ)*(base19) + (794127731/100000000000000 : ℝ)*(base23) + (110368857/100000000000000 : ℝ)*(upper3) + (1768397/3125000000000 : ℝ)*(lower4) + (93974387/100000000000000 : ℝ)*(upper5) + (1729747374751733/50000000000000 : ℝ)*(major0) + (1729747374751733/50000000000000 : ℝ)*(major1) + (1729747374751733/50000000000000 : ℝ)*(major2) + (9928976837/100000000000000 : ℝ)*(sp1) + (431269827/3125000000000 : ℝ)*(sp2) + (4845237502330131/100000000000000 : ℝ)*(sp4) + (4845226941954073/100000000000000 : ℝ)*(sp5) + (75706607930749/1562500000000 : ℝ)*(sp6) + (2073751819805233/100000000000000 : ℝ)*(sp7) + (2073751819805233/100000000000000 : ℝ)*(f.failure) + (4845237502330131/100000000000000 : ℝ)*(f.sum) + (416329406567/175546875000000000000000000 : ℝ)*base65 + (1249952165116516727/374500000000000000000000000000000 : ℝ)*base68 + (219302017526516727/374500000000000000000000000000000 : ℝ)*base70 + (416767933654483273/374500000000000000000000000000000 : ℝ)*base71 + (20456863625677/11235000000000000000000000000 : ℝ)*base74 + (1276203825670516727/374500000000000000000000000000000 : ℝ)*base76 + (1925462666097983273/374500000000000000000000000000000 : ℝ)*base77 + (1957441791551016727/374500000000000000000000000000000 : ℝ)*base80 + (34354679940893/11235000000000000000000000000 : ℝ)*base81 + (13225949/2500000000000000000000 : ℝ)*base90 + (13225949/2500000000000000000000 : ℝ)*base92 + (13225949/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1555_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1555_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1555_s5_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-903155283/5000000000 : ℝ)*x 0 + (5427711391/10000000000 : ℝ)*x 1 + (1043902591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903155283/5000000000 : ℝ)^4607 ≤ (2215226464991/20000000000000 : ℝ)^3583 := by
    have hnat : (903155283 : ℕ)^4607*20000000000000^3583 ≤ 2215226464991^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903155283 5000000000 2215226464991 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427711391/10000000000 : ℝ)^4607 ≤ (45579735225847/100000000000000 : ℝ)^3583 := by
    have hnat : (5427711391 : ℕ)^4607*100000000000000^3583 ≤ 45579735225847^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427711391 10000000000 45579735225847 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043902591/2000000000 : ℝ)^4607 ≤ (2709008276861/6250000000000 : ℝ)^3583 := by
    have hnat : (1043902591 : ℕ)^4607*6250000000000^3583 ≤ 2709008276861^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043902591 2000000000 2709008276861 6250000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903155283/5000000000 : ℝ), (5427711391/10000000000 : ℝ), (1043902591/2000000000 : ℝ)] ![(2215226464991/20000000000000 : ℝ), (45579735225847/100000000000000 : ℝ), (2709008276861/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903155283/5000000000 : ℝ)|^4607 ≤ (2215226464991/20000000000000 : ℝ)^3583
        have hw : |(-903155283/5000000000 : ℝ)|=(903155283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427711391/10000000000 : ℝ)|^4607 ≤ (45579735225847/100000000000000 : ℝ)^3583
        have hw : |(5427711391/10000000000 : ℝ)|=(5427711391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043902591/2000000000 : ℝ)|^4607 ≤ (2709008276861/6250000000000 : ℝ)^3583
        have hw : |(1043902591/2000000000 : ℝ)|=(1043902591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s5_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674552739/5000000000 : ℝ)*x 0 + (-1912851421/10000000000 : ℝ)*x 1 + (163109781/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674552739/5000000000 : ℝ)^4607 ≤ (44732744117291/100000000000000 : ℝ)^3583 := by
    have hnat : (2674552739 : ℕ)^4607*100000000000000^3583 ≤ 44732744117291^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674552739 5000000000 44732744117291 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912851421/10000000000 : ℝ)^4607 ≤ (11923123048549/100000000000000 : ℝ)^3583 := by
    have hnat : (1912851421 : ℕ)^4607*100000000000000^3583 ≤ 11923123048549^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912851421 10000000000 11923123048549 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163109781/312500000 : ℝ)^4607 ≤ (8668826564969/20000000000000 : ℝ)^3583 := by
    have hnat : (163109781 : ℕ)^4607*20000000000000^3583 ≤ 8668826564969^3583*312500000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163109781 312500000 8668826564969 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674552739/5000000000 : ℝ), (-1912851421/10000000000 : ℝ), (163109781/312500000 : ℝ)] ![(44732744117291/100000000000000 : ℝ), (11923123048549/100000000000000 : ℝ), (8668826564969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674552739/5000000000 : ℝ)|^4607 ≤ (44732744117291/100000000000000 : ℝ)^3583
        have hw : |(2674552739/5000000000 : ℝ)|=(2674552739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912851421/10000000000 : ℝ)|^4607 ≤ (11923123048549/100000000000000 : ℝ)^3583
        have hw : |(-1912851421/10000000000 : ℝ)|=(1912851421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163109781/312500000 : ℝ)|^4607 ≤ (8668826564969/20000000000000 : ℝ)^3583
        have hw : |(163109781/312500000 : ℝ)|=(163109781/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s5_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26745527/50000000 : ℝ)*x 0 + (1043902623/2000000000 : ℝ)*x 1 + (-956425681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26745527/50000000 : ℝ)^4607 ≤ (5591592909823/12500000000000 : ℝ)^3583 := by
    have hnat : (26745527 : ℕ)^4607*12500000000000^3583 ≤ 5591592909823^3583*50000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26745527 50000000 5591592909823 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043902623/2000000000 : ℝ)^4607 ≤ (5418016767273/12500000000000 : ℝ)^3583 := by
    have hnat : (1043902623 : ℕ)^4607*12500000000000^3583 ≤ 5418016767273^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043902623 2000000000 5418016767273 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956425681/5000000000 : ℝ)^4607 ≤ (11923122575689/100000000000000 : ℝ)^3583 := by
    have hnat : (956425681 : ℕ)^4607*100000000000000^3583 ≤ 11923122575689^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956425681 5000000000 11923122575689 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26745527/50000000 : ℝ), (1043902623/2000000000 : ℝ), (-956425681/5000000000 : ℝ)] ![(5591592909823/12500000000000 : ℝ), (5418016767273/12500000000000 : ℝ), (11923122575689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26745527/50000000 : ℝ)|^4607 ≤ (5591592909823/12500000000000 : ℝ)^3583
        have hw : |(26745527/50000000 : ℝ)|=(26745527/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043902623/2000000000 : ℝ)|^4607 ≤ (5418016767273/12500000000000 : ℝ)^3583
        have hw : |(1043902623/2000000000 : ℝ)|=(1043902623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-956425681/5000000000 : ℝ)|^4607 ≤ (11923122575689/100000000000000 : ℝ)^3583
        have hw : |(-956425681/5000000000 : ℝ)|=(956425681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s5_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170006299/400000000 : ℝ)*x 0 + (32101107/80000000 : ℝ)*x 1 + (562385711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170006299/400000000 : ℝ)^4607 ≤ (33281691927777/100000000000000 : ℝ)^3583 := by
    have hnat : (170006299 : ℕ)^4607*100000000000000^3583 ≤ 33281691927777^3583*400000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170006299 400000000 33281691927777 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32101107/80000000 : ℝ)^4607 ≤ (15454775311907/50000000000000 : ℝ)^3583 := by
    have hnat : (32101107 : ℕ)^4607*50000000000000^3583 ≤ 15454775311907^3583*80000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32101107 80000000 15454775311907 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562385711/1250000000 : ℝ)^4607 ≤ (17904378718757/50000000000000 : ℝ)^3583 := by
    have hnat : (562385711 : ℕ)^4607*50000000000000^3583 ≤ 17904378718757^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562385711 1250000000 17904378718757 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170006299/400000000 : ℝ), (32101107/80000000 : ℝ), (562385711/1250000000 : ℝ)] ![(33281691927777/100000000000000 : ℝ), (15454775311907/50000000000000 : ℝ), (17904378718757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170006299/400000000 : ℝ)|^4607 ≤ (33281691927777/100000000000000 : ℝ)^3583
        have hw : |(170006299/400000000 : ℝ)|=(170006299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32101107/80000000 : ℝ)|^4607 ≤ (15454775311907/50000000000000 : ℝ)^3583
        have hw : |(32101107/80000000 : ℝ)|=(32101107/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562385711/1250000000 : ℝ)|^4607 ≤ (17904378718757/50000000000000 : ℝ)^3583
        have hw : |(562385711/1250000000 : ℝ)|=(562385711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s5_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-180633807/1000000000 : ℝ)*x 0 + (5220594109/10000000000 : ℝ)*x 1 + (5426622109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180633807/1000000000 : ℝ)^4607 ≤ (11076349177199/100000000000000 : ℝ)^3583 := by
    have hnat : (180633807 : ℕ)^4607*100000000000000^3583 ≤ 11076349177199^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180633807 1000000000 11076349177199 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220594109/10000000000 : ℝ)^4607 ≤ (43355676850671/100000000000000 : ℝ)^3583 := by
    have hnat : (5220594109 : ℕ)^4607*100000000000000^3583 ≤ 43355676850671^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220594109 10000000000 43355676850671 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426622109/10000000000 : ℝ)^4607 ≤ (45567973952949/100000000000000 : ℝ)^3583 := by
    have hnat : (5426622109 : ℕ)^4607*100000000000000^3583 ≤ 45567973952949^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426622109 10000000000 45567973952949 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-180633807/1000000000 : ℝ), (5220594109/10000000000 : ℝ), (5426622109/10000000000 : ℝ)] ![(11076349177199/100000000000000 : ℝ), (43355676850671/100000000000000 : ℝ), (45567973952949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-180633807/1000000000 : ℝ)|^4607 ≤ (11076349177199/100000000000000 : ℝ)^3583
        have hw : |(-180633807/1000000000 : ℝ)|=(180633807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220594109/10000000000 : ℝ)|^4607 ≤ (43355676850671/100000000000000 : ℝ)^3583
        have hw : |(5220594109/10000000000 : ℝ)|=(5220594109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426622109/10000000000 : ℝ)|^4607 ≤ (45567973952949/100000000000000 : ℝ)^3583
        have hw : |(5426622109/10000000000 : ℝ)|=(5426622109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s5_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294123869/10000000000 : ℝ)*x 0 + (-1705742407/10000000000 : ℝ)*x 1 + (339163883/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294123869/10000000000 : ℝ)^4607 ≤ (4414241622723/10000000000000 : ℝ)^3583 := by
    have hnat : (5294123869 : ℕ)^4607*10000000000000^3583 ≤ 4414241622723^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294123869 10000000000 4414241622723 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1705742407/10000000000 : ℝ)^4607 ≤ (1028960959717/10000000000000 : ℝ)^3583 := by
    have hnat : (1705742407 : ℕ)^4607*10000000000000^3583 ≤ 1028960959717^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705742407 10000000000 1028960959717 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339163883/625000000 : ℝ)^4607 ≤ (45567974158091/100000000000000 : ℝ)^3583 := by
    have hnat : (339163883 : ℕ)^4607*100000000000000^3583 ≤ 45567974158091^3583*625000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339163883 625000000 45567974158091 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294123869/10000000000 : ℝ), (-1705742407/10000000000 : ℝ), (339163883/625000000 : ℝ)] ![(4414241622723/10000000000000 : ℝ), (1028960959717/10000000000000 : ℝ), (45567974158091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294123869/10000000000 : ℝ)|^4607 ≤ (4414241622723/10000000000000 : ℝ)^3583
        have hw : |(5294123869/10000000000 : ℝ)|=(5294123869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1705742407/10000000000 : ℝ)|^4607 ≤ (1028960959717/10000000000000 : ℝ)^3583
        have hw : |(-1705742407/10000000000 : ℝ)|=(1705742407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339163883/625000000 : ℝ)|^4607 ≤ (45567974158091/100000000000000 : ℝ)^3583
        have hw : |(339163883/625000000 : ℝ)|=(339163883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s5_6 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294123879/10000000000 : ℝ)*x 0 + (1356655553/2500000000 : ℝ)*x 1 + (-426435569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294123879/10000000000 : ℝ)^4607 ≤ (1103560408361/2500000000000 : ℝ)^3583 := by
    have hnat : (5294123879 : ℕ)^4607*2500000000000^3583 ≤ 1103560408361^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294123879 10000000000 1103560408361 2500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356655553/2500000000 : ℝ)^4607 ≤ (11391993766259/25000000000000 : ℝ)^3583 := by
    have hnat : (1356655553 : ℕ)^4607*25000000000000^3583 ≤ 11391993766259^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356655553 2500000000 11391993766259 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426435569/2500000000 : ℝ)^4607 ≤ (10289608581089/100000000000000 : ℝ)^3583 := by
    have hnat : (426435569 : ℕ)^4607*100000000000000^3583 ≤ 10289608581089^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426435569 2500000000 10289608581089 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294123879/10000000000 : ℝ), (1356655553/2500000000 : ℝ), (-426435569/2500000000 : ℝ)] ![(1103560408361/2500000000000 : ℝ), (11391993766259/25000000000000 : ℝ), (10289608581089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294123879/10000000000 : ℝ)|^4607 ≤ (1103560408361/2500000000000 : ℝ)^3583
        have hw : |(5294123879/10000000000 : ℝ)|=(5294123879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356655553/2500000000 : ℝ)|^4607 ≤ (11391993766259/25000000000000 : ℝ)^3583
        have hw : |(1356655553/2500000000 : ℝ)|=(1356655553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426435569/2500000000 : ℝ)|^4607 ≤ (10289608581089/100000000000000 : ℝ)^3583
        have hw : |(-426435569/2500000000 : ℝ)|=(426435569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s5_7 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125110673/5000000000 : ℝ)*x 0 + (4496559539/10000000000 : ℝ)*x 1 + (401518313/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125110673/5000000000 : ℝ)^4607 ≤ (33282335024693/100000000000000 : ℝ)^3583 := by
    have hnat : (2125110673 : ℕ)^4607*100000000000000^3583 ≤ 33282335024693^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125110673 5000000000 33282335024693 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496559539/10000000000 : ℝ)^4607 ≤ (35782907440189/100000000000000 : ℝ)^3583 := by
    have hnat : (4496559539 : ℕ)^4607*100000000000000^3583 ≤ 35782907440189^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496559539 10000000000 35782907440189 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401518313/1000000000 : ℝ)^4607 ≤ (3093475752151/10000000000000 : ℝ)^3583 := by
    have hnat : (401518313 : ℕ)^4607*10000000000000^3583 ≤ 3093475752151^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401518313 1000000000 3093475752151 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125110673/5000000000 : ℝ), (4496559539/10000000000 : ℝ), (401518313/1000000000 : ℝ)] ![(33282335024693/100000000000000 : ℝ), (35782907440189/100000000000000 : ℝ), (3093475752151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125110673/5000000000 : ℝ)|^4607 ≤ (33282335024693/100000000000000 : ℝ)^3583
        have hw : |(2125110673/5000000000 : ℝ)|=(2125110673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496559539/10000000000 : ℝ)|^4607 ≤ (35782907440189/100000000000000 : ℝ)^3583
        have hw : |(4496559539/10000000000 : ℝ)|=(4496559539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401518313/1000000000 : ℝ)|^4607 ≤ (3093475752151/10000000000000 : ℝ)^3583
        have hw : |(401518313/1000000000 : ℝ)|=(401518313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11071/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2767/25000 : ℝ) ^ (4605/1024 : ℝ) ≤ (5024718725536371/100000000000000000000 : ℝ) := by
    have hpowers : (2767/25000 : ℝ)^4605 ≤ (5024718725536371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2767 : ℕ)^4605*100000000000000000000^1024 ≤ 5024718725536371^1024*25000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2767 25000 5024718725536371 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2767/25000 : ℝ)) (X := (5024718725536371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4605/1024 : ℝ) ≤ (11388019225650279/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4605 ≤ (11388019225650279/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4605*50000000000000000000^1024 ≤ 11388019225650279^1024*100000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 11388019225650279 50000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (11388019225650279/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005024718725536371/50000000000000000000 : ℝ) ≤ (10000223457586957/10000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50005024718725536371/50000000000000000000 : ℝ)^1024 ≤ (10000223457586957/10000000000000000 : ℝ)^4605 := by
      have hnat : (50005024718725536371 : ℕ)^1024*10000000000000000^4605 ≤ 10000223457586957^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005024718725536371 50000000000000000000 10000223457586957 10000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000223457586957/10000000000000000 : ℝ)) (X := (50005024718725536371/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027800757176836929/100000000000000000000 : ℝ) ≤ (5000309065131819/5000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (100027800757176836929/100000000000000000000 : ℝ)^1024 ≤ (5000309065131819/5000000000000000 : ℝ)^4605 := by
      have hnat : (100027800757176836929 : ℕ)^1024*5000000000000000^4605 ≤ 5000309065131819^4605*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027800757176836929 100000000000000000000 5000309065131819 5000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000309065131819/5000000000000000 : ℝ)) (X := (100027800757176836929/100000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011388019225650279/25000000000000000000 : ℝ) ≤ (10001012802940319/10000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (25011388019225650279/25000000000000000000 : ℝ)^1024 ≤ (10001012802940319/10000000000000000 : ℝ)^4605 := by
      have hnat : (25011388019225650279 : ℕ)^1024*10000000000000000^4605 ≤ 10001012802940319^4605*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011388019225650279 25000000000000000000 10001012802940319 10000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001012802940319/10000000000000000 : ℝ)) (X := (25011388019225650279/25000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5024718725536371/100000000000000000000 : ℝ) ≤ ((44202251431620926281/44210000000000000000 : ℝ)+2*(394672676681/442100000000000 : ℝ)*(2767/25000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (44202251431620926281/44210000000000000000 : ℝ)+2*(394672676681/442100000000000 : ℝ)*(2767/25000 : ℝ)=(10000223457586957/10000000000000000 : ℝ) by norm_num, show 1+2*(5024718725536371/100000000000000000000 : ℝ)=(50005024718725536371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11388019225650279/50000000000000000000 : ℝ)+(5024718725536371/100000000000000000000 : ℝ) ≤ ((44202251431620926281/44210000000000000000 : ℝ)+(394672676681/442100000000000 : ℝ)*((15489/100000 : ℝ)+(2767/25000 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (44202251431620926281/44210000000000000000 : ℝ)+(394672676681/442100000000000 : ℝ)*((15489/100000 : ℝ)+(2767/25000 : ℝ))=(5000309065131819/5000000000000000 : ℝ) by norm_num, show 1+(11388019225650279/50000000000000000000 : ℝ)+(5024718725536371/100000000000000000000 : ℝ)=(100027800757176836929/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11388019225650279/50000000000000000000 : ℝ) ≤ ((44202251431620926281/44210000000000000000 : ℝ)+2*(394672676681/442100000000000 : ℝ)*(15489/100000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (44202251431620926281/44210000000000000000 : ℝ)+2*(394672676681/442100000000000 : ℝ)*(15489/100000 : ℝ)=(10001012802940319/10000000000000000 : ℝ) by norm_num, show 1+2*(11388019225650279/50000000000000000000 : ℝ)=(25011388019225650279/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44202251431620926281/44210000000000000000 : ℝ)*(X 1 0+X 2 0)+(394672676681/442100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (44202251431620926281/44210000000000000000 : ℝ)) (alpha := (394672676681/442100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44202251431620926281/44210000000000000000 : ℝ)*(X 0 1+X 2 1)+(394672676681/442100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (44202251431620926281/44210000000000000000 : ℝ)) (alpha := (394672676681/442100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44202251431620926281/44210000000000000000 : ℝ)*(X 0 2+X 1 2)+(394672676681/442100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (44202251431620926281/44210000000000000000 : ℝ)) (alpha := (394672676681/442100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-903155283/5000000000 : ℝ)*X 0 0+(5427711391/10000000000 : ℝ)*X 0 1+(1043902591/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674552739/5000000000 : ℝ)*X 1 0+(-1912851421/10000000000 : ℝ)*X 1 1+(163109781/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((26745527/50000000 : ℝ)*X 2 0+(1043902623/2000000000 : ℝ)*X 2 1+(-956425681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((170006299/400000000 : ℝ)*X 0 0+(32101107/80000000 : ℝ)*X 0 1+(562385711/1250000000 : ℝ)*X 0 2+(170006299/400000000 : ℝ)*X 1 0+(32101107/80000000 : ℝ)*X 1 1+(562385711/1250000000 : ℝ)*X 1 2+(170006299/400000000 : ℝ)*X 2 0+(32101107/80000000 : ℝ)*X 2 1+(562385711/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-180633807/1000000000 : ℝ)*X 0 0+(5220594109/10000000000 : ℝ)*X 0 1+(5426622109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294123869/10000000000 : ℝ)*X 1 0+(-1705742407/10000000000 : ℝ)*X 1 1+(339163883/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294123879/10000000000 : ℝ)*X 2 0+(1356655553/2500000000 : ℝ)*X 2 1+(-426435569/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2125110673/5000000000 : ℝ)*X 0 0+(4496559539/10000000000 : ℝ)*X 0 1+(401518313/1000000000 : ℝ)*X 0 2+(2125110673/5000000000 : ℝ)*X 1 0+(4496559539/10000000000 : ℝ)*X 1 1+(401518313/1000000000 : ℝ)*X 1 2+(2125110673/5000000000 : ℝ)*X 2 0+(4496559539/10000000000 : ℝ)*X 2 1+(401518313/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1591547494477914942970063149/138156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224063999/12500000000000 : ℝ)*(base19) + (189874473/12500000000000 : ℝ)*(base23) + (27210499/25000000000000 : ℝ)*(lower2) + (54525813/20000000000000 : ℝ)*(upper3) + (21711993/12500000000000 : ℝ)*(upper5) + (214341135471969/6250000000000 : ℝ)*(major0) + (214341135471969/6250000000000 : ℝ)*(major1) + (214341135471969/6250000000000 : ℝ)*(major2) + (4803140123774651/100000000000000 : ℝ)*(sp0) + (960633480101687/20000000000000 : ℝ)*(sp1) + (4803167674024643/100000000000000 : ℝ)*(sp2) + (2055733081833251/100000000000000 : ℝ)*(sp3) + (1162769831/4000000000000 : ℝ)*(sp4) + (13676252333/100000000000000 : ℝ)*(sp7) + (128484172380349/6250000000000 : ℝ)*(f.failure) + (4803169193020427/100000000000000 : ℝ)*(f.sum) + (106639958612111/22105000000000000000000000000 : ℝ)*base66 + (2387214128480567289/276312500000000000000000000000000 : ℝ)*base67 + (3175603727909942289/276312500000000000000000000000000 : ℝ)*base69 + (4745304310315254789/276312500000000000000000000000000 : ℝ)*base71 + (107896423390861/22105000000000000000000000000 : ℝ)*base74 + (1815277407463692289/276312500000000000000000000000000 : ℝ)*base75 + (2545672987898379789/276312500000000000000000000000000 : ℝ)*base77 + (2446951805348754789/276312500000000000000000000000000 : ℝ)*base79 + (11412803097991/5526250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1834297/156250000000000000000 : ℝ)*base90 + (1834297/156250000000000000000 : ℝ)*base92 + (1834297/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (790960080113686779747700443/138156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389915133/50000000000000 : ℝ)*(base19) + (85001461/10000000000000 : ℝ)*(base23) + (183254597/100000000000000 : ℝ)*(lower1) + (2681/39062500000 : ℝ)*(upper2) + (182613283/100000000000000 : ℝ)*(upper3) + (130201639/100000000000000 : ℝ)*(upper5) + (433192021841299/12500000000000 : ℝ)*(major0) + (433192021841299/12500000000000 : ℝ)*(major1) + (433192021841299/12500000000000 : ℝ)*(major2) + (462690063/10000000000000 : ℝ)*(sp2) + (2426849440174799/50000000000000 : ℝ)*(sp4) + (1213424525129833/25000000000000 : ℝ)*(sp5) + (2426846701717179/50000000000000 : ℝ)*(sp6) + (207737327827409/10000000000000 : ℝ)*(sp7) + (207737327827409/10000000000000 : ℝ)*(f.failure) + (2426849440174799/50000000000000 : ℝ)*(f.sum) + (13350574668181/2763125000000000000000000000 : ℝ)*base66 + (1407400192255679019/552625000000000000000000000000000 : ℝ)*base67 + (10479785265368070981/552625000000000000000000000000000 : ℝ)*base70 + (4462975471821179019/552625000000000000000000000000000 : ℝ)*base71 + (8641918501789/11052500000000000000000000000 : ℝ)*base74 + (10980347606607679019/552625000000000000000000000000000 : ℝ)*base75 + (2442522560539429019/552625000000000000000000000000000 : ℝ)*base77 + (8528413116125179019/552625000000000000000000000000000 : ℝ)*base79 + (68995202565301/2763125000000000000000000000 : ℝ)*base82 + (580477/250000000000000000000 : ℝ)*base90 + (580477/250000000000000000000 : ℝ)*base92 + (580477/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1555_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1555_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1555_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1555_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1555_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1555_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1555_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
