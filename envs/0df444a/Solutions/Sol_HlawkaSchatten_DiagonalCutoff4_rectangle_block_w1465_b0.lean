-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1465_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:43.835711+00:00
-- url     : https://prove2.me/submissions/29c1dffc-2669-4d3e-befb-60a05c4b5d86

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
theorem support_rectangle_w1465_s0_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-868419899/5000000000 : ℝ)*x 0 + (1487486337/2500000000 : ℝ)*x 1 + (4834703019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868419899/5000000000 : ℝ)^4427 ≤ (410256180849/4000000000000 : ℝ)^3403 := by
    have hnat : (868419899 : ℕ)^4427*4000000000000^3403 ≤ 410256180849^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868419899 5000000000 410256180849 4000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1487486337/2500000000 : ℝ)^4427 ≤ (3180837458207/6250000000000 : ℝ)^3403 := by
    have hnat : (1487486337 : ℕ)^4427*6250000000000^3403 ≤ 3180837458207^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487486337 2500000000 3180837458207 6250000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4834703019/10000000000 : ℝ)^4427 ≤ (9712549032977/25000000000000 : ℝ)^3403 := by
    have hnat : (4834703019 : ℕ)^4427*25000000000000^3403 ≤ 9712549032977^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4834703019 10000000000 9712549032977 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-868419899/5000000000 : ℝ), (1487486337/2500000000 : ℝ), (4834703019/10000000000 : ℝ)] ![(410256180849/4000000000000 : ℝ), (3180837458207/6250000000000 : ℝ), (9712549032977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-868419899/5000000000 : ℝ)|^4427 ≤ (410256180849/4000000000000 : ℝ)^3403
        have hw : |(-868419899/5000000000 : ℝ)|=(868419899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1487486337/2500000000 : ℝ)|^4427 ≤ (3180837458207/6250000000000 : ℝ)^3403
        have hw : |(1487486337/2500000000 : ℝ)|=(1487486337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4834703019/10000000000 : ℝ)|^4427 ≤ (9712549032977/25000000000000 : ℝ)^3403
        have hw : |(4834703019/10000000000 : ℝ)|=(4834703019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s0_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1097654999/2000000000 : ℝ)*x 0 + (-147865803/625000000 : ℝ)*x 1 + (1208675759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097654999/2000000000 : ℝ)^4427 ≤ (45817275381601/100000000000000 : ℝ)^3403 := by
    have hnat : (1097654999 : ℕ)^4427*100000000000000^3403 ≤ 45817275381601^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097654999 2000000000 45817275381601 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147865803/625000000 : ℝ)^4427 ≤ (3066505657981/20000000000000 : ℝ)^3403 := by
    have hnat : (147865803 : ℕ)^4427*20000000000000^3403 ≤ 3066505657981^3403*625000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147865803 625000000 3066505657981 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208675759/2500000000 : ℝ)^4427 ≤ (19425098154811/50000000000000 : ℝ)^3403 := by
    have hnat : (1208675759 : ℕ)^4427*50000000000000^3403 ≤ 19425098154811^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208675759 2500000000 19425098154811 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097654999/2000000000 : ℝ), (-147865803/625000000 : ℝ), (1208675759/2500000000 : ℝ)] ![(45817275381601/100000000000000 : ℝ), (3066505657981/20000000000000 : ℝ), (19425098154811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097654999/2000000000 : ℝ)|^4427 ≤ (45817275381601/100000000000000 : ℝ)^3403
        have hw : |(1097654999/2000000000 : ℝ)|=(1097654999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147865803/625000000 : ℝ)|^4427 ≤ (3066505657981/20000000000000 : ℝ)^3403
        have hw : |(-147865803/625000000 : ℝ)|=(147865803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208675759/2500000000 : ℝ)|^4427 ≤ (19425098154811/50000000000000 : ℝ)^3403
        have hw : |(1208675759/2500000000 : ℝ)|=(1208675759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s0_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2744137479/5000000000 : ℝ)*x 0 + (4834703057/10000000000 : ℝ)*x 1 + (-236585287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744137479/5000000000 : ℝ)^4427 ≤ (45817274979771/100000000000000 : ℝ)^3403 := by
    have hnat : (2744137479 : ℕ)^4427*100000000000000^3403 ≤ 45817274979771^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744137479 5000000000 45817274979771 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4834703057/10000000000 : ℝ)^4427 ≤ (777003930583/2000000000000 : ℝ)^3403 := by
    have hnat : (4834703057 : ℕ)^4427*2000000000000^3403 ≤ 777003930583^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4834703057 10000000000 777003930583 2000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236585287/1000000000 : ℝ)^4427 ≤ (3066505695077/20000000000000 : ℝ)^3403 := by
    have hnat : (236585287 : ℕ)^4427*20000000000000^3403 ≤ 3066505695077^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236585287 1000000000 3066505695077 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2744137479/5000000000 : ℝ), (4834703057/10000000000 : ℝ), (-236585287/1000000000 : ℝ)] ![(45817274979771/100000000000000 : ℝ), (777003930583/2000000000000 : ℝ), (3066505695077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2744137479/5000000000 : ℝ)|^4427 ≤ (45817274979771/100000000000000 : ℝ)^3403
        have hw : |(2744137479/5000000000 : ℝ)|=(2744137479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4834703057/10000000000 : ℝ)|^4427 ≤ (777003930583/2000000000000 : ℝ)^3403
        have hw : |(4834703057/10000000000 : ℝ)|=(4834703057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-236585287/1000000000 : ℝ)|^4427 ≤ (3066505695077/20000000000000 : ℝ)^3403
        have hw : |(-236585287/1000000000 : ℝ)|=(236585287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s0_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4158068979/10000000000 : ℝ)*x 0 + (3091917501/10000000000 : ℝ)*x 1 + (22149207/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4158068979/10000000000 : ℝ)^4427 ≤ (798274084603/2500000000000 : ℝ)^3403 := by
    have hnat : (4158068979 : ℕ)^4427*2500000000000^3403 ≤ 798274084603^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158068979 10000000000 798274084603 2500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091917501/10000000000 : ℝ)^4427 ≤ (5429650718389/25000000000000 : ℝ)^3403 := by
    have hnat : (3091917501 : ℕ)^4427*25000000000000^3403 ≤ 5429650718389^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091917501 10000000000 5429650718389 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22149207/40000000 : ℝ)^4427 ≤ (46350433733043/100000000000000 : ℝ)^3403 := by
    have hnat : (22149207 : ℕ)^4427*100000000000000^3403 ≤ 46350433733043^3403*40000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22149207 40000000 46350433733043 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4158068979/10000000000 : ℝ), (3091917501/10000000000 : ℝ), (22149207/40000000 : ℝ)] ![(798274084603/2500000000000 : ℝ), (5429650718389/25000000000000 : ℝ), (46350433733043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4158068979/10000000000 : ℝ)|^4427 ≤ (798274084603/2500000000000 : ℝ)^3403
        have hw : |(4158068979/10000000000 : ℝ)|=(4158068979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091917501/10000000000 : ℝ)|^4427 ≤ (5429650718389/25000000000000 : ℝ)^3403
        have hw : |(3091917501/10000000000 : ℝ)|=(3091917501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22149207/40000000 : ℝ)|^4427 ≤ (46350433733043/100000000000000 : ℝ)^3403
        have hw : |(22149207/40000000 : ℝ)|=(22149207/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s0_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-34815651/200000000 : ℝ)*x 0 + (972676863/2000000000 : ℝ)*x 1 + (5920231339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34815651/200000000 : ℝ)^4427 ≤ (5143351842423/50000000000000 : ℝ)^3403 := by
    have hnat : (34815651 : ℕ)^4427*50000000000000^3403 ≤ 5143351842423^3403*200000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34815651 200000000 5143351842423 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972676863/2000000000 : ℝ)^4427 ≤ (9787572424569/25000000000000 : ℝ)^3403 := by
    have hnat : (972676863 : ℕ)^4427*25000000000000^3403 ≤ 9787572424569^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972676863 2000000000 9787572424569 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5920231339/10000000000 : ℝ)^4427 ≤ (25281503299551/50000000000000 : ℝ)^3403 := by
    have hnat : (5920231339 : ℕ)^4427*50000000000000^3403 ≤ 25281503299551^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920231339 10000000000 25281503299551 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34815651/200000000 : ℝ), (972676863/2000000000 : ℝ), (5920231339/10000000000 : ℝ)] ![(5143351842423/50000000000000 : ℝ), (9787572424569/25000000000000 : ℝ), (25281503299551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34815651/200000000 : ℝ)|^4427 ≤ (5143351842423/50000000000000 : ℝ)^3403
        have hw : |(-34815651/200000000 : ℝ)|=(34815651/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(972676863/2000000000 : ℝ)|^4427 ≤ (9787572424569/25000000000000 : ℝ)^3403
        have hw : |(972676863/2000000000 : ℝ)|=(972676863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5920231339/10000000000 : ℝ)|^4427 ≤ (25281503299551/50000000000000 : ℝ)^3403
        have hw : |(5920231339/10000000000 : ℝ)|=(5920231339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s0_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591935509/5000000000 : ℝ)*x 0 + (-640162187/5000000000 : ℝ)*x 1 + (1480057851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591935509/5000000000 : ℝ)^4427 ≤ (21269658093143/50000000000000 : ℝ)^3403 := by
    have hnat : (2591935509 : ℕ)^4427*50000000000000^3403 ≤ 21269658093143^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591935509 5000000000 21269658093143 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640162187/5000000000 : ℝ)^4427 ≤ (1724419119707/25000000000000 : ℝ)^3403 := by
    have hnat : (640162187 : ℕ)^4427*25000000000000^3403 ≤ 1724419119707^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640162187 5000000000 1724419119707 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1480057851/2500000000 : ℝ)^4427 ≤ (25281503660649/50000000000000 : ℝ)^3403 := by
    have hnat : (1480057851 : ℕ)^4427*50000000000000^3403 ≤ 25281503660649^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480057851 2500000000 25281503660649 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591935509/5000000000 : ℝ), (-640162187/5000000000 : ℝ), (1480057851/2500000000 : ℝ)] ![(21269658093143/50000000000000 : ℝ), (1724419119707/25000000000000 : ℝ), (25281503660649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591935509/5000000000 : ℝ)|^4427 ≤ (21269658093143/50000000000000 : ℝ)^3403
        have hw : |(2591935509/5000000000 : ℝ)|=(2591935509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-640162187/5000000000 : ℝ)|^4427 ≤ (1724419119707/25000000000000 : ℝ)^3403
        have hw : |(-640162187/5000000000 : ℝ)|=(640162187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1480057851/2500000000 : ℝ)|^4427 ≤ (25281503660649/50000000000000 : ℝ)^3403
        have hw : |(1480057851/2500000000 : ℝ)|=(1480057851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s0_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183871053/10000000000 : ℝ)*x 0 + (5920231249/10000000000 : ℝ)*x 1 + (-256064913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183871053/10000000000 : ℝ)^4427 ≤ (1701572662397/4000000000000 : ℝ)^3403 := by
    have hnat : (5183871053 : ℕ)^4427*4000000000000^3403 ≤ 1701572662397^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183871053 10000000000 1701572662397 4000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5920231249/10000000000 : ℝ)^4427 ≤ (25281502799569/50000000000000 : ℝ)^3403 := by
    have hnat : (5920231249 : ℕ)^4427*50000000000000^3403 ≤ 25281502799569^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920231249 10000000000 25281502799569 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256064913/2000000000 : ℝ)^4427 ≤ (6897677817467/100000000000000 : ℝ)^3403 := by
    have hnat : (256064913 : ℕ)^4427*100000000000000^3403 ≤ 6897677817467^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256064913 2000000000 6897677817467 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183871053/10000000000 : ℝ), (5920231249/10000000000 : ℝ), (-256064913/2000000000 : ℝ)] ![(1701572662397/4000000000000 : ℝ), (25281502799569/50000000000000 : ℝ), (6897677817467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183871053/10000000000 : ℝ)|^4427 ≤ (1701572662397/4000000000000 : ℝ)^3403
        have hw : |(5183871053/10000000000 : ℝ)|=(5183871053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5920231249/10000000000 : ℝ)|^4427 ≤ (25281502799569/50000000000000 : ℝ)^3403
        have hw : |(5920231249/10000000000 : ℝ)|=(5920231249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256064913/2000000000 : ℝ)|^4427 ≤ (6897677817467/100000000000000 : ℝ)^3403
        have hw : |(-256064913/2000000000 : ℝ)|=(256064913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s0_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833342961/2000000000 : ℝ)*x 0 + (5474412331/10000000000 : ℝ)*x 1 + (3157071279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833342961/2000000000 : ℝ)^4427 ≤ (32017362674163/100000000000000 : ℝ)^3403 := by
    have hnat : (833342961 : ℕ)^4427*100000000000000^3403 ≤ 32017362674163^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833342961 2000000000 32017362674163 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474412331/10000000000 : ℝ)^4427 ≤ (45666780236021/100000000000000 : ℝ)^3403 := by
    have hnat : (5474412331 : ℕ)^4427*100000000000000^3403 ≤ 45666780236021^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474412331 10000000000 45666780236021 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3157071279/10000000000 : ℝ)^4427 ≤ (11157928535209/50000000000000 : ℝ)^3403 := by
    have hnat : (3157071279 : ℕ)^4427*50000000000000^3403 ≤ 11157928535209^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3157071279 10000000000 11157928535209 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833342961/2000000000 : ℝ), (5474412331/10000000000 : ℝ), (3157071279/10000000000 : ℝ)] ![(32017362674163/100000000000000 : ℝ), (45666780236021/100000000000000 : ℝ), (11157928535209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833342961/2000000000 : ℝ)|^4427 ≤ (32017362674163/100000000000000 : ℝ)^3403
        have hw : |(833342961/2000000000 : ℝ)|=(833342961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474412331/10000000000 : ℝ)|^4427 ≤ (45666780236021/100000000000000 : ℝ)^3403
        have hw : |(5474412331/10000000000 : ℝ)|=(5474412331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3157071279/10000000000 : ℝ)|^4427 ≤ (11157928535209/50000000000000 : ℝ)^3403
        have hw : |(3157071279/10000000000 : ℝ)|=(3157071279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26107/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4425/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4425 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4425*1^1024 ≤ 0^1024*1^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4425/1024 : ℝ) ≤ (953577943850675613/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4425 ≤ (953577943850675613/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4425*50000000000000000000^1024 ≤ 953577943850675613^1024*5^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 953577943850675613 50000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (953577943850675613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4425 := by
      have hnat : (1 : ℕ)^1024*1^4425 ≤ 1^4425*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50953577943850675613/50000000000000000000 : ℝ) ≤ (10043814085769843/10000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (50953577943850675613/50000000000000000000 : ℝ)^1024 ≤ (10043814085769843/10000000000000000 : ℝ)^4425 := by
      have hnat : (50953577943850675613 : ℕ)^1024*10000000000000000^4425 ≤ 10043814085769843^4425*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50953577943850675613 50000000000000000000 10043814085769843 10000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10043814085769843/10000000000000000 : ℝ)) (X := (50953577943850675613/50000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25953577943850675613/25000000000000000000 : ℝ) ≤ (5043814085769843/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (25953577943850675613/25000000000000000000 : ℝ)^1024 ≤ (5043814085769843/5000000000000000 : ℝ)^4425 := by
      have hnat : (25953577943850675613 : ℕ)^1024*5000000000000000^4425 ≤ 5043814085769843^4425*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25953577943850675613 25000000000000000000 5043814085769843 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043814085769843/5000000000000000 : ℝ)) (X := (25953577943850675613/25000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(43814085769843/4000000000000000 : ℝ)*(0 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43814085769843/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(953577943850675613/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(43814085769843/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (1 : ℝ)+(43814085769843/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10043814085769843/10000000000000000 : ℝ) by norm_num, show 1+(953577943850675613/50000000000000000000 : ℝ)+(0 : ℝ)=(50953577943850675613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(953577943850675613/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(43814085769843/4000000000000000 : ℝ)*(2/5 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43814085769843/4000000000000000 : ℝ)*(2/5 : ℝ)=(5043814085769843/5000000000000000 : ℝ) by norm_num, show 1+2*(953577943850675613/50000000000000000000 : ℝ)=(25953577943850675613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(43814085769843/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43814085769843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(43814085769843/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43814085769843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(43814085769843/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43814085769843/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-868419899/5000000000 : ℝ)*X 0 0+(1487486337/2500000000 : ℝ)*X 0 1+(4834703019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1097654999/2000000000 : ℝ)*X 1 0+(-147865803/625000000 : ℝ)*X 1 1+(1208675759/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2744137479/5000000000 : ℝ)*X 2 0+(4834703057/10000000000 : ℝ)*X 2 1+(-236585287/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4158068979/10000000000 : ℝ)*X 0 0+(3091917501/10000000000 : ℝ)*X 0 1+(22149207/40000000 : ℝ)*X 0 2+(4158068979/10000000000 : ℝ)*X 1 0+(3091917501/10000000000 : ℝ)*X 1 1+(22149207/40000000 : ℝ)*X 1 2+(4158068979/10000000000 : ℝ)*X 2 0+(3091917501/10000000000 : ℝ)*X 2 1+(22149207/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-34815651/200000000 : ℝ)*X 0 0+(972676863/2000000000 : ℝ)*X 0 1+(5920231339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591935509/5000000000 : ℝ)*X 1 0+(-640162187/5000000000 : ℝ)*X 1 1+(1480057851/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183871053/10000000000 : ℝ)*X 2 0+(5920231249/10000000000 : ℝ)*X 2 1+(-256064913/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((833342961/2000000000 : ℝ)*X 0 0+(5474412331/10000000000 : ℝ)*X 0 1+(3157071279/10000000000 : ℝ)*X 0 2+(833342961/2000000000 : ℝ)*X 1 0+(5474412331/10000000000 : ℝ)*X 1 1+(3157071279/10000000000 : ℝ)*X 1 2+(833342961/2000000000 : ℝ)*X 2 0+(5474412331/10000000000 : ℝ)*X 2 1+(3157071279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (156176304775609188218247/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8760411/12500000000000 : ℝ)*(base1) + (176770557/10000000000000 : ℝ)*(base19) + (880830249/50000000000000 : ℝ)*(base23) + (112117929/50000000000000 : ℝ)*(upper3) + (422849/195312500000 : ℝ)*(upper5) + (130561731307819/20000000000000 : ℝ)*(major0) + (130561731307819/20000000000000 : ℝ)*(major1) + (130561731307819/20000000000000 : ℝ)*(major2) + (89667189838457/10000000000000 : ℝ)*(sp0) + (448338054068473/50000000000000 : ℝ)*(sp1) + (896676114182017/100000000000000 : ℝ)*(sp2) + (81787263117589/20000000000000 : ℝ)*(sp3) + (3023770617/50000000000000 : ℝ)*(sp4) + (279127059/10000000000000 : ℝ)*(sp7) + (408939176941823/100000000000000 : ℝ)*(f.failure) + (224169468960629/25000000000000 : ℝ)*(f.sum) + (108659438502417/40000000000000000000000000000 : ℝ)*base65 + (454418155902417/80000000000000000000000000000 : ℝ)*base67 + (61158819022417/80000000000000000000000000000 : ℝ)*base69 + (207153150302417/80000000000000000000000000000 : ℝ)*base71 + (232319879222417/40000000000000000000000000000 : ℝ)*base73 + (228645307022417/80000000000000000000000000000 : ℝ)*base75 + (544147949022417/80000000000000000000000000000 : ℝ)*base77 + (781898083982417/80000000000000000000000000000 : ℝ)*base79 + (13267837502417/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (49749233/5000000000000000000000 : ℝ)*base90 + (49749233/5000000000000000000000 : ℝ)*base92 + (49749233/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168337430272290226567869/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61315153/4000000000000 : ℝ)*(base19) + (1547101283/100000000000000 : ℝ)*(base23) + (1124759/781250000000 : ℝ)*(base32) + (11580723/5000000000000 : ℝ)*(upper3) + (141482357/100000000000000 : ℝ)*(upper5) + (172217395575461/25000000000000 : ℝ)*(major0) + (172217395575461/25000000000000 : ℝ)*(major1) + (172217395575461/25000000000000 : ℝ)*(major2) + (921014611/25000000000000 : ℝ)*(sp1) + (3817467879/100000000000000 : ℝ)*(sp2) + (236552525915997/25000000000000 : ℝ)*(sp4) + (946204886726719/100000000000000 : ℝ)*(sp5) + (473102369547413/50000000000000 : ℝ)*(sp6) + (431528692520631/100000000000000 : ℝ)*(sp7) + (215764418244891/50000000000000 : ℝ)*(f.failure) + (236552525915997/25000000000000 : ℝ)*(f.sum) + (461443127377/50000000000000000000000000000 : ℝ)*base66 + (80154723477377/100000000000000000000000000000 : ℝ)*base68 + (355792486522623/100000000000000000000000000000 : ℝ)*base69 + (649652216922623/100000000000000000000000000000 : ℝ)*base71 + (294854987527377/50000000000000000000000000000 : ℝ)*base74 + (544332533722623/100000000000000000000000000000 : ℝ)*base75 + (712211403122623/100000000000000000000000000000 : ℝ)*base77 + (299202279177377/100000000000000000000000000000 : ℝ)*base80 + (120764496827377/50000000000000000000000000000 : ℝ)*base82 + (32483861/2500000000000000000000 : ℝ)*base90 + (32483861/2500000000000000000000 : ℝ)*base92 + (32483861/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1465_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1465_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1465_s1_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1903393649/10000000000 : ℝ)*x 0 + (5603842721/10000000000 : ℝ)*x 1 + (5073957629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1903393649/10000000000 : ℝ)^4427 ≤ (2888490131009/25000000000000 : ℝ)^3403 := by
    have hnat : (1903393649 : ℕ)^4427*25000000000000^3403 ≤ 2888490131009^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903393649 10000000000 2888490131009 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5603842721/10000000000 : ℝ)^4427 ≤ (9415266022901/20000000000000 : ℝ)^3403 := by
    have hnat : (5603842721 : ℕ)^4427*20000000000000^3403 ≤ 9415266022901^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603842721 10000000000 9415266022901 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073957629/10000000000 : ℝ)^4427 ≤ (20684854670631/50000000000000 : ℝ)^3403 := by
    have hnat : (5073957629 : ℕ)^4427*50000000000000^3403 ≤ 20684854670631^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073957629 10000000000 20684854670631 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1903393649/10000000000 : ℝ), (5603842721/10000000000 : ℝ), (5073957629/10000000000 : ℝ)] ![(2888490131009/25000000000000 : ℝ), (9415266022901/20000000000000 : ℝ), (20684854670631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1903393649/10000000000 : ℝ)|^4427 ≤ (2888490131009/25000000000000 : ℝ)^3403
        have hw : |(-1903393649/10000000000 : ℝ)|=(1903393649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5603842721/10000000000 : ℝ)|^4427 ≤ (9415266022901/20000000000000 : ℝ)^3403
        have hw : |(5603842721/10000000000 : ℝ)|=(5603842721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073957629/10000000000 : ℝ)|^4427 ≤ (20684854670631/50000000000000 : ℝ)^3403
        have hw : |(5073957629/10000000000 : ℝ)|=(5073957629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s1_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395426679/10000000000 : ℝ)*x 0 + (-273020933/1250000000 : ℝ)*x 1 + (5073958857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395426679/10000000000 : ℝ)^4427 ≤ (44811493607249/100000000000000 : ℝ)^3403 := by
    have hnat : (5395426679 : ℕ)^4427*100000000000000^3403 ≤ 44811493607249^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395426679 10000000000 44811493607249 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273020933/1250000000 : ℝ)^4427 ≤ (13818784009803/100000000000000 : ℝ)^3403 := by
    have hnat : (273020933 : ℕ)^4427*100000000000000^3403 ≤ 13818784009803^3403*1250000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273020933 1250000000 13818784009803 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073958857/10000000000 : ℝ)^4427 ≤ (41369722366377/100000000000000 : ℝ)^3403 := by
    have hnat : (5073958857 : ℕ)^4427*100000000000000^3403 ≤ 41369722366377^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073958857 10000000000 41369722366377 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395426679/10000000000 : ℝ), (-273020933/1250000000 : ℝ), (5073958857/10000000000 : ℝ)] ![(44811493607249/100000000000000 : ℝ), (13818784009803/100000000000000 : ℝ), (41369722366377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395426679/10000000000 : ℝ)|^4427 ≤ (44811493607249/100000000000000 : ℝ)^3403
        have hw : |(5395426679/10000000000 : ℝ)|=(5395426679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273020933/1250000000 : ℝ)|^4427 ≤ (13818784009803/100000000000000 : ℝ)^3403
        have hw : |(-273020933/1250000000 : ℝ)|=(273020933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073958857/10000000000 : ℝ)|^4427 ≤ (41369722366377/100000000000000 : ℝ)^3403
        have hw : |(5073958857/10000000000 : ℝ)|=(5073958857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s1_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395427707/10000000000 : ℝ)*x 0 + (2536978869/5000000000 : ℝ)*x 1 + (-1092083779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395427707/10000000000 : ℝ)^4427 ≤ (22405752357221/50000000000000 : ℝ)^3403 := by
    have hnat : (5395427707 : ℕ)^4427*50000000000000^3403 ≤ 22405752357221^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395427707 10000000000 22405752357221 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536978869/5000000000 : ℝ)^4427 ≤ (206848552487/500000000000 : ℝ)^3403 := by
    have hnat : (2536978869 : ℕ)^4427*500000000000^3403 ≤ 206848552487^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536978869 5000000000 206848552487 500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092083779/5000000000 : ℝ)^4427 ≤ (13818784783479/100000000000000 : ℝ)^3403 := by
    have hnat : (1092083779 : ℕ)^4427*100000000000000^3403 ≤ 13818784783479^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092083779 5000000000 13818784783479 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395427707/10000000000 : ℝ), (2536978869/5000000000 : ℝ), (-1092083779/5000000000 : ℝ)] ![(22405752357221/50000000000000 : ℝ), (206848552487/500000000000 : ℝ), (13818784783479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395427707/10000000000 : ℝ)|^4427 ≤ (22405752357221/50000000000000 : ℝ)^3403
        have hw : |(5395427707/10000000000 : ℝ)|=(5395427707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536978869/5000000000 : ℝ)|^4427 ≤ (206848552487/500000000000 : ℝ)^3403
        have hw : |(2536978869/5000000000 : ℝ)|=(2536978869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092083779/5000000000 : ℝ)|^4427 ≤ (13818784783479/100000000000000 : ℝ)^3403
        have hw : |(-1092083779/5000000000 : ℝ)|=(1092083779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s1_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266703287/10000000000 : ℝ)*x 0 + (930120769/2500000000 : ℝ)*x 1 + (1220588971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266703287/10000000000 : ℝ)^4427 ≤ (33020466446863/100000000000000 : ℝ)^3403 := by
    have hnat : (4266703287 : ℕ)^4427*100000000000000^3403 ≤ 33020466446863^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266703287 10000000000 33020466446863 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (930120769/2500000000 : ℝ)^4427 ≤ (2763045051169/10000000000000 : ℝ)^3403 := by
    have hnat : (930120769 : ℕ)^4427*10000000000000^3403 ≤ 2763045051169^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930120769 2500000000 2763045051169 10000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1220588971/2500000000 : ℝ)^4427 ≤ (7869816604799/20000000000000 : ℝ)^3403 := by
    have hnat : (1220588971 : ℕ)^4427*20000000000000^3403 ≤ 7869816604799^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220588971 2500000000 7869816604799 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266703287/10000000000 : ℝ), (930120769/2500000000 : ℝ), (1220588971/2500000000 : ℝ)] ![(33020466446863/100000000000000 : ℝ), (2763045051169/10000000000000 : ℝ), (7869816604799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266703287/10000000000 : ℝ)|^4427 ≤ (33020466446863/100000000000000 : ℝ)^3403
        have hw : |(4266703287/10000000000 : ℝ)|=(4266703287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(930120769/2500000000 : ℝ)|^4427 ≤ (2763045051169/10000000000000 : ℝ)^3403
        have hw : |(930120769/2500000000 : ℝ)|=(930120769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1220588971/2500000000 : ℝ)|^4427 ≤ (7869816604799/20000000000000 : ℝ)^3403
        have hw : |(1220588971/2500000000 : ℝ)|=(1220588971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s1_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-475950063/2500000000 : ℝ)*x 0 + (5080291821/10000000000 : ℝ)*x 1 + (223895959/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475950063/2500000000 : ℝ)^4427 ≤ (11557171480169/100000000000000 : ℝ)^3403 := by
    have hnat : (475950063 : ℕ)^4427*100000000000000^3403 ≤ 11557171480169^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475950063 2500000000 11557171480169 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080291821/10000000000 : ℝ)^4427 ≤ (41436907282781/100000000000000 : ℝ)^3403 := by
    have hnat : (5080291821 : ℕ)^4427*100000000000000^3403 ≤ 41436907282781^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080291821 10000000000 41436907282781 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223895959/400000000 : ℝ)^4427 ≤ (47005921226453/100000000000000 : ℝ)^3403 := by
    have hnat : (223895959 : ℕ)^4427*100000000000000^3403 ≤ 47005921226453^3403*400000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223895959 400000000 47005921226453 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-475950063/2500000000 : ℝ), (5080291821/10000000000 : ℝ), (223895959/400000000 : ℝ)] ![(11557171480169/100000000000000 : ℝ), (41436907282781/100000000000000 : ℝ), (47005921226453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-475950063/2500000000 : ℝ)|^4427 ≤ (11557171480169/100000000000000 : ℝ)^3403
        have hw : |(-475950063/2500000000 : ℝ)|=(475950063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080291821/10000000000 : ℝ)|^4427 ≤ (41436907282781/100000000000000 : ℝ)^3403
        have hw : |(5080291821/10000000000 : ℝ)|=(5080291821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223895959/400000000 : ℝ)|^4427 ≤ (47005921226453/100000000000000 : ℝ)^3403
        have hw : |(223895959/400000000 : ℝ)|=(223895959/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s1_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256705199/10000000000 : ℝ)*x 0 + (-415181781/2500000000 : ℝ)*x 1 + (2798699493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256705199/10000000000 : ℝ)^4427 ≤ (8663697604187/20000000000000 : ℝ)^3403 := by
    have hnat : (5256705199 : ℕ)^4427*20000000000000^3403 ≤ 8663697604187^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256705199 10000000000 8663697604187 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415181781/2500000000 : ℝ)^4427 ≤ (9675590618509/100000000000000 : ℝ)^3403 := by
    have hnat : (415181781 : ℕ)^4427*100000000000000^3403 ≤ 9675590618509^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415181781 2500000000 9675590618509 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2798699493/5000000000 : ℝ)^4427 ≤ (23502960673313/50000000000000 : ℝ)^3403 := by
    have hnat : (2798699493 : ℕ)^4427*50000000000000^3403 ≤ 23502960673313^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2798699493 5000000000 23502960673313 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256705199/10000000000 : ℝ), (-415181781/2500000000 : ℝ), (2798699493/5000000000 : ℝ)] ![(8663697604187/20000000000000 : ℝ), (9675590618509/100000000000000 : ℝ), (23502960673313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256705199/10000000000 : ℝ)|^4427 ≤ (8663697604187/20000000000000 : ℝ)^3403
        have hw : |(5256705199/10000000000 : ℝ)|=(5256705199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415181781/2500000000 : ℝ)|^4427 ≤ (9675590618509/100000000000000 : ℝ)^3403
        have hw : |(-415181781/2500000000 : ℝ)|=(415181781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2798699493/5000000000 : ℝ)|^4427 ≤ (23502960673313/50000000000000 : ℝ)^3403
        have hw : |(2798699493/5000000000 : ℝ)|=(2798699493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s1_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525670527/1000000000 : ℝ)*x 0 + (1119479789/2000000000 : ℝ)*x 1 + (-830363541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525670527/1000000000 : ℝ)^4427 ≤ (43318488782077/100000000000000 : ℝ)^3403 := by
    have hnat : (525670527 : ℕ)^4427*100000000000000^3403 ≤ 43318488782077^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525670527 1000000000 43318488782077 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119479789/2000000000 : ℝ)^4427 ≤ (11751480224677/25000000000000 : ℝ)^3403 := by
    have hnat : (1119479789 : ℕ)^4427*25000000000000^3403 ≤ 11751480224677^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119479789 2000000000 11751480224677 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830363541/5000000000 : ℝ)^4427 ≤ (9675590300181/100000000000000 : ℝ)^3403 := by
    have hnat : (830363541 : ℕ)^4427*100000000000000^3403 ≤ 9675590300181^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830363541 5000000000 9675590300181 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525670527/1000000000 : ℝ), (1119479789/2000000000 : ℝ), (-830363541/5000000000 : ℝ)] ![(43318488782077/100000000000000 : ℝ), (11751480224677/25000000000000 : ℝ), (9675590300181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525670527/1000000000 : ℝ)|^4427 ≤ (43318488782077/100000000000000 : ℝ)^3403
        have hw : |(525670527/1000000000 : ℝ)|=(525670527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119479789/2000000000 : ℝ)|^4427 ≤ (11751480224677/25000000000000 : ℝ)^3403
        have hw : |(1119479789/2000000000 : ℝ)|=(1119479789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-830363541/5000000000 : ℝ)|^4427 ≤ (9675590300181/100000000000000 : ℝ)^3403
        have hw : |(-830363541/5000000000 : ℝ)|=(830363541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s1_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4267595297/10000000000 : ℝ)*x 0 + (4868467941/10000000000 : ℝ)*x 1 + (3734610411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267595297/10000000000 : ℝ)^4427 ≤ (33029447385253/100000000000000 : ℝ)^3403 := by
    have hnat : (4267595297 : ℕ)^4427*100000000000000^3403 ≤ 33029447385253^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267595297 10000000000 33029447385253 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4868467941/10000000000 : ℝ)^4427 ≤ (39203535556859/100000000000000 : ℝ)^3403 := by
    have hnat : (4868467941 : ℕ)^4427*100000000000000^3403 ≤ 39203535556859^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868467941 10000000000 39203535556859 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3734610411/10000000000 : ℝ)^4427 ≤ (27767017041661/100000000000000 : ℝ)^3403 := by
    have hnat : (3734610411 : ℕ)^4427*100000000000000^3403 ≤ 27767017041661^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734610411 10000000000 27767017041661 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267595297/10000000000 : ℝ), (4868467941/10000000000 : ℝ), (3734610411/10000000000 : ℝ)] ![(33029447385253/100000000000000 : ℝ), (39203535556859/100000000000000 : ℝ), (27767017041661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267595297/10000000000 : ℝ)|^4427 ≤ (33029447385253/100000000000000 : ℝ)^3403
        have hw : |(4267595297/10000000000 : ℝ)|=(4267595297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4868467941/10000000000 : ℝ)|^4427 ≤ (39203535556859/100000000000000 : ℝ)^3403
        have hw : |(4868467941/10000000000 : ℝ)|=(4868467941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3734610411/10000000000 : ℝ)|^4427 ≤ (27767017041661/100000000000000 : ℝ)^3403
        have hw : |(3734610411/10000000000 : ℝ)|=(3734610411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7679/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18879/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2201/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (215194981551/3125000000000000000 : ℝ) := by
    have hpowers : (2201/100000 : ℝ)^4425 ≤ (215194981551/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2201 : ℕ)^4425*3125000000000000000^1024 ≤ 215194981551^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 100000 215194981551 3125000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/100000 : ℝ)) (X := (215194981551/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26107/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (60348748157731703/20000000000000000000 : ℝ) := by
    have hpowers : (26107/100000 : ℝ)^4425 ≤ (60348748157731703/20000000000000000000 : ℝ)^1024 := by
      have hnat : (26107 : ℕ)^4425*20000000000000000000^1024 ≤ 60348748157731703^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26107 100000 60348748157731703 20000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26107/100000 : ℝ)) (X := (60348748157731703/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500215194981551/1562500000000000000 : ℝ) ≤ (5000000159356131/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (1562500215194981551/1562500000000000000 : ℝ)^1024 ≤ (5000000159356131/5000000000000000 : ℝ)^4425 := by
      have hnat : (1562500215194981551 : ℕ)^1024*5000000000000000^4425 ≤ 5000000159356131^4425*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500215194981551 1562500000000000000 5000000159356131 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000159356131/5000000000000000 : ℝ)) (X := (1562500215194981551/1562500000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100301750627028068147/100000000000000000000 : ℝ) ≤ (2501743700381527/2500000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (100301750627028068147/100000000000000000000 : ℝ)^1024 ≤ (2501743700381527/2500000000000000 : ℝ)^4425 := by
      have hnat : (100301750627028068147 : ℕ)^1024*2500000000000000^4425 ≤ 2501743700381527^4425*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100301750627028068147 100000000000000000000 2501743700381527 2500000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501743700381527/2500000000000000 : ℝ)) (X := (100301750627028068147/100000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10060348748157731703/10000000000000000000 : ℝ) ≤ (5006974642169977/5000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (10060348748157731703/10000000000000000000 : ℝ)^1024 ≤ (5006974642169977/5000000000000000 : ℝ)^4425 := by
      have hnat : (10060348748157731703 : ℕ)^1024*5000000000000000^4425 ≤ 5006974642169977^4425*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10060348748157731703 10000000000000000000 5006974642169977 5000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006974642169977/5000000000000000 : ℝ)) (X := (10060348748157731703/10000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(215194981551/3125000000000000000 : ℝ) ≤ ((373483290540294977/373531250000000000 : ℝ)+2*(3487241406923/1195300000000000 : ℝ)*(2201/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (373483290540294977/373531250000000000 : ℝ)+2*(3487241406923/1195300000000000 : ℝ)*(2201/100000 : ℝ)=(5000000159356131/5000000000000000 : ℝ) by norm_num, show 1+2*(215194981551/3125000000000000000 : ℝ)=(1562500215194981551/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60348748157731703/20000000000000000000 : ℝ)+(215194981551/3125000000000000000 : ℝ) ≤ ((373483290540294977/373531250000000000 : ℝ)+(3487241406923/1195300000000000 : ℝ)*((26107/100000 : ℝ)+(2201/100000 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (373483290540294977/373531250000000000 : ℝ)+(3487241406923/1195300000000000 : ℝ)*((26107/100000 : ℝ)+(2201/100000 : ℝ))=(2501743700381527/2500000000000000 : ℝ) by norm_num, show 1+(60348748157731703/20000000000000000000 : ℝ)+(215194981551/3125000000000000000 : ℝ)=(100301750627028068147/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60348748157731703/20000000000000000000 : ℝ) ≤ ((373483290540294977/373531250000000000 : ℝ)+2*(3487241406923/1195300000000000 : ℝ)*(26107/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (373483290540294977/373531250000000000 : ℝ)+2*(3487241406923/1195300000000000 : ℝ)*(26107/100000 : ℝ)=(5006974642169977/5000000000000000 : ℝ) by norm_num, show 1+2*(60348748157731703/20000000000000000000 : ℝ)=(10060348748157731703/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (373483290540294977/373531250000000000 : ℝ)*(X 1 0+X 2 0)+(3487241406923/1195300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (2201/100000 : ℝ)) (hi := (26107/100000 : ℝ)) (c := (373483290540294977/373531250000000000 : ℝ)) (alpha := (3487241406923/1195300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (373483290540294977/373531250000000000 : ℝ)*(X 0 1+X 2 1)+(3487241406923/1195300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (2201/100000 : ℝ)) (hi := (26107/100000 : ℝ)) (c := (373483290540294977/373531250000000000 : ℝ)) (alpha := (3487241406923/1195300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (373483290540294977/373531250000000000 : ℝ)*(X 0 2+X 1 2)+(3487241406923/1195300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (2201/100000 : ℝ)) (hi := (26107/100000 : ℝ)) (c := (373483290540294977/373531250000000000 : ℝ)) (alpha := (3487241406923/1195300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1903393649/10000000000 : ℝ)*X 0 0+(5603842721/10000000000 : ℝ)*X 0 1+(5073957629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395426679/10000000000 : ℝ)*X 1 0+(-273020933/1250000000 : ℝ)*X 1 1+(5073958857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395427707/10000000000 : ℝ)*X 2 0+(2536978869/5000000000 : ℝ)*X 2 1+(-1092083779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266703287/10000000000 : ℝ)*X 0 0+(930120769/2500000000 : ℝ)*X 0 1+(1220588971/2500000000 : ℝ)*X 0 2+(4266703287/10000000000 : ℝ)*X 1 0+(930120769/2500000000 : ℝ)*X 1 1+(1220588971/2500000000 : ℝ)*X 1 2+(4266703287/10000000000 : ℝ)*X 2 0+(930120769/2500000000 : ℝ)*X 2 1+(1220588971/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-475950063/2500000000 : ℝ)*X 0 0+(5080291821/10000000000 : ℝ)*X 0 1+(223895959/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256705199/10000000000 : ℝ)*X 1 0+(-415181781/2500000000 : ℝ)*X 1 1+(2798699493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525670527/1000000000 : ℝ)*X 2 0+(1119479789/2000000000 : ℝ)*X 2 1+(-830363541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267595297/10000000000 : ℝ)*X 0 0+(4868467941/10000000000 : ℝ)*X 0 1+(3734610411/10000000000 : ℝ)*X 0 2+(4267595297/10000000000 : ℝ)*X 1 0+(4868467941/10000000000 : ℝ)*X 1 1+(3734610411/10000000000 : ℝ)*X 1 2+(4267595297/10000000000 : ℝ)*X 2 0+(4868467941/10000000000 : ℝ)*X 2 1+(3734610411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (484497711325242148207509/59765000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4420793/50000000000000 : ℝ)*(base1) + (1387002961/100000000000000 : ℝ)*(base19) + (873289897/50000000000000 : ℝ)*(base23) + (25664499/20000000000000 : ℝ)*(upper3) + (82258947/50000000000000 : ℝ)*(upper5) + (1373960264616637/100000000000000 : ℝ)*(major0) + (1373960264616637/100000000000000 : ℝ)*(major1) + (1373960264616637/100000000000000 : ℝ)*(major2) + (1887214869484081/100000000000000 : ℝ)*(sp0) + (1887228416794341/100000000000000 : ℝ)*(sp1) + (471807014304377/25000000000000 : ℝ)*(sp2) + (860684752423997/100000000000000 : ℝ)*(sp3) + (14943154807/100000000000000 : ℝ)*(sp4) + (711743327/12500000000000 : ℝ)*(sp7) + (860690455212199/100000000000000 : ℝ)*(f.failure) + (943614901898651/50000000000000 : ℝ)*(f.sum) + (45136108614919/59765000000000000000000000000 : ℝ)*base66 + (253497583812634073/74706250000000000000000000000000 : ℝ)*base67 + (33226790810278427/74706250000000000000000000000000 : ℝ)*base70 + (331192363662246573/74706250000000000000000000000000 : ℝ)*base71 + (26014957029109/59765000000000000000000000000 : ℝ)*base74 + (183558286980522177/74706250000000000000000000000000 : ℝ)*base76 + (34948243119009677/74706250000000000000000000000000 : ℝ)*base78 + (15220583305959073/74706250000000000000000000000000 : ℝ)*base79 + (43924785737949/59765000000000000000000000000 : ℝ)*base82 + (2396471/5000000000000000000000 : ℝ)*base89 + (2396471/5000000000000000000000 : ℝ)*base91 + (2396471/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (270317635685029955799266187/37353125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1375747667/100000000000000 : ℝ)*(base19) + (749595561/50000000000000 : ℝ)*(base23) + (186210421/100000000000000 : ℝ)*(upper3) + (38986753/100000000000000 : ℝ)*(lower4) + (81141033/50000000000000 : ℝ)*(upper5) + (87993125427407/6250000000000 : ℝ)*(major0) + (87993125427407/6250000000000 : ℝ)*(major1) + (87993125427407/6250000000000 : ℝ)*(major2) + (402723809/5000000000000 : ℝ)*(sp1) + (4465986349/50000000000000 : ℝ)*(sp2) + (966917347906059/50000000000000 : ℝ)*(sp4) + (193382526558827/10000000000000 : ℝ)*(sp5) + (966912132324149/50000000000000 : ℝ)*(sp6) + (881945076637751/100000000000000 : ℝ)*(sp7) + (881945076637751/100000000000000 : ℝ)*(f.failure) + (966917347906059/50000000000000 : ℝ)*(f.sum) + (76174466063339/59765000000000000000000000000 : ℝ)*base66 + (303708238838756099/37353125000000000000000000000000 : ℝ)*base67 + (60031903281012651/37353125000000000000000000000000 : ℝ)*base70 + (167464529717243599/37353125000000000000000000000000 : ℝ)*base71 + (166328333815961/59765000000000000000000000000 : ℝ)*base73 + (346659903554018599/37353125000000000000000000000000 : ℝ)*base75 + (14113068129156099/37353125000000000000000000000000 : ℝ)*base77 + (131323721755106099/37353125000000000000000000000000 : ℝ)*base79 + (136291149022289/59765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (14612921/5000000000000000000000 : ℝ)*base90 + (14612921/5000000000000000000000 : ℝ)*base92 + (14612921/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1465_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7679/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18879/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1465_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1465_s2_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-386771249/2000000000 : ℝ)*x 0 + (1368661741/2500000000 : ℝ)*x 1 + (5183520993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (386771249/2000000000 : ℝ)^4427 ≤ (5897546965469/50000000000000 : ℝ)^3403 := by
    have hnat : (386771249 : ℕ)^4427*50000000000000^3403 ≤ 5897546965469^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386771249 2000000000 5897546965469 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368661741/2500000000 : ℝ)^4427 ≤ (9133865298743/20000000000000 : ℝ)^3403 := by
    have hnat : (1368661741 : ℕ)^4427*20000000000000^3403 ≤ 9133865298743^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368661741 2500000000 9133865298743 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183520993/10000000000 : ℝ)^4427 ≤ (5316947446207/12500000000000 : ℝ)^3403 := by
    have hnat : (5183520993 : ℕ)^4427*12500000000000^3403 ≤ 5316947446207^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183520993 10000000000 5316947446207 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-386771249/2000000000 : ℝ), (1368661741/2500000000 : ℝ), (5183520993/10000000000 : ℝ)] ![(5897546965469/50000000000000 : ℝ), (9133865298743/20000000000000 : ℝ), (5316947446207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-386771249/2000000000 : ℝ)|^4427 ≤ (5897546965469/50000000000000 : ℝ)^3403
        have hw : |(-386771249/2000000000 : ℝ)|=(386771249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368661741/2500000000 : ℝ)|^4427 ≤ (9133865298743/20000000000000 : ℝ)^3403
        have hw : |(1368661741/2500000000 : ℝ)|=(1368661741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183520993/10000000000 : ℝ)|^4427 ≤ (5316947446207/12500000000000 : ℝ)^3403
        have hw : |(5183520993/10000000000 : ℝ)|=(5183520993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s2_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681558521/5000000000 : ℝ)*x 0 + (-13026229/62500000 : ℝ)*x 1 + (5183522343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681558521/5000000000 : ℝ)^4427 ≤ (4446271385733/10000000000000 : ℝ)^3403 := by
    have hnat : (2681558521 : ℕ)^4427*10000000000000^3403 ≤ 4446271385733^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681558521 5000000000 4446271385733 10000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13026229/62500000 : ℝ)^4427 ≤ (3250423036581/25000000000000 : ℝ)^3403 := by
    have hnat : (13026229 : ℕ)^4427*25000000000000^3403 ≤ 3250423036581^3403*62500000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13026229 62500000 3250423036581 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183522343/10000000000 : ℝ)^4427 ≤ (8507118796229/20000000000000 : ℝ)^3403 := by
    have hnat : (5183522343 : ℕ)^4427*20000000000000^3403 ≤ 8507118796229^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183522343 10000000000 8507118796229 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681558521/5000000000 : ℝ), (-13026229/62500000 : ℝ), (5183522343/10000000000 : ℝ)] ![(4446271385733/10000000000000 : ℝ), (3250423036581/25000000000000 : ℝ), (8507118796229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681558521/5000000000 : ℝ)|^4427 ≤ (4446271385733/10000000000000 : ℝ)^3403
        have hw : |(2681558521/5000000000 : ℝ)|=(2681558521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13026229/62500000 : ℝ)|^4427 ≤ (3250423036581/25000000000000 : ℝ)^3403
        have hw : |(-13026229/62500000 : ℝ)|=(13026229/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183522343/10000000000 : ℝ)|^4427 ≤ (8507118796229/20000000000000 : ℝ)^3403
        have hw : |(5183522343/10000000000 : ℝ)|=(5183522343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s2_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536311797/1000000000 : ℝ)*x 0 + (259176077/500000000 : ℝ)*x 1 + (-2084196463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536311797/1000000000 : ℝ)^4427 ≤ (44462723865951/100000000000000 : ℝ)^3403 := by
    have hnat : (536311797 : ℕ)^4427*100000000000000^3403 ≤ 44462723865951^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536311797 1000000000 44462723865951 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259176077/500000000 : ℝ)^4427 ≤ (21267792704489/50000000000000 : ℝ)^3403 := by
    have hnat : (259176077 : ℕ)^4427*50000000000000^3403 ≤ 21267792704489^3403*500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259176077 500000000 21267792704489 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084196463/10000000000 : ℝ)^4427 ≤ (6500845354951/50000000000000 : ℝ)^3403 := by
    have hnat : (2084196463 : ℕ)^4427*50000000000000^3403 ≤ 6500845354951^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084196463 10000000000 6500845354951 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536311797/1000000000 : ℝ), (259176077/500000000 : ℝ), (-2084196463/10000000000 : ℝ)] ![(44462723865951/100000000000000 : ℝ), (21267792704489/50000000000000 : ℝ), (6500845354951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536311797/1000000000 : ℝ)|^4427 ≤ (44462723865951/100000000000000 : ℝ)^3403
        have hw : |(536311797/1000000000 : ℝ)|=(536311797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259176077/500000000 : ℝ)|^4427 ≤ (21267792704489/50000000000000 : ℝ)^3403
        have hw : |(259176077/500000000 : ℝ)|=(259176077/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084196463/10000000000 : ℝ)|^4427 ≤ (6500845354951/50000000000000 : ℝ)^3403
        have hw : |(-2084196463/10000000000 : ℝ)|=(2084196463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s2_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072095021/2500000000 : ℝ)*x 0 + (994920973/2500000000 : ℝ)*x 1 + (4618032833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072095021/2500000000 : ℝ)^4427 ≤ (2077429538243/6250000000000 : ℝ)^3403 := by
    have hnat : (1072095021 : ℕ)^4427*6250000000000^3403 ≤ 2077429538243^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072095021 2500000000 2077429538243 6250000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994920973/2500000000 : ℝ)^4427 ≤ (15080253164471/50000000000000 : ℝ)^3403 := by
    have hnat : (994920973 : ℕ)^4427*50000000000000^3403 ≤ 15080253164471^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994920973 2500000000 15080253164471 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4618032833/10000000000 : ℝ)^4427 ≤ (1143769407731/3125000000000 : ℝ)^3403 := by
    have hnat : (4618032833 : ℕ)^4427*3125000000000^3403 ≤ 1143769407731^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618032833 10000000000 1143769407731 3125000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072095021/2500000000 : ℝ), (994920973/2500000000 : ℝ), (4618032833/10000000000 : ℝ)] ![(2077429538243/6250000000000 : ℝ), (15080253164471/50000000000000 : ℝ), (1143769407731/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072095021/2500000000 : ℝ)|^4427 ≤ (2077429538243/6250000000000 : ℝ)^3403
        have hw : |(1072095021/2500000000 : ℝ)|=(1072095021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994920973/2500000000 : ℝ)|^4427 ≤ (15080253164471/50000000000000 : ℝ)^3403
        have hw : |(994920973/2500000000 : ℝ)|=(994920973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4618032833/10000000000 : ℝ)|^4427 ≤ (1143769407731/3125000000000 : ℝ)^3403
        have hw : |(4618032833/10000000000 : ℝ)|=(4618032833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s2_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1933923477/10000000000 : ℝ)*x 0 + (1037088609/2000000000 : ℝ)*x 1 + (547270689/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933923477/10000000000 : ℝ)^4427 ≤ (11795627392451/100000000000000 : ℝ)^3403 := by
    have hnat : (1933923477 : ℕ)^4427*100000000000000^3403 ≤ 11795627392451^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933923477 10000000000 11795627392451 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037088609/2000000000 : ℝ)^4427 ≤ (8511219791733/20000000000000 : ℝ)^3403 := by
    have hnat : (1037088609 : ℕ)^4427*20000000000000^3403 ≤ 8511219791733^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037088609 2000000000 8511219791733 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547270689/1000000000 : ℝ)^4427 ≤ (9129654725811/20000000000000 : ℝ)^3403 := by
    have hnat : (547270689 : ℕ)^4427*20000000000000^3403 ≤ 9129654725811^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547270689 1000000000 9129654725811 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1933923477/10000000000 : ℝ), (1037088609/2000000000 : ℝ), (547270689/1000000000 : ℝ)] ![(11795627392451/100000000000000 : ℝ), (8511219791733/20000000000000 : ℝ), (9129654725811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1933923477/10000000000 : ℝ)|^4427 ≤ (11795627392451/100000000000000 : ℝ)^3403
        have hw : |(-1933923477/10000000000 : ℝ)|=(1933923477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037088609/2000000000 : ℝ)|^4427 ≤ (8511219791733/20000000000000 : ℝ)^3403
        have hw : |(1037088609/2000000000 : ℝ)|=(1037088609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547270689/1000000000 : ℝ)|^4427 ≤ (9129654725811/20000000000000 : ℝ)^3403
        have hw : |(547270689/1000000000 : ℝ)|=(547270689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s2_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287247753/10000000000 : ℝ)*x 0 + (-179501189/1000000000 : ℝ)*x 1 + (547270697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287247753/10000000000 : ℝ)^4427 ≤ (43646199431503/100000000000000 : ℝ)^3403 := by
    have hnat : (5287247753 : ℕ)^4427*100000000000000^3403 ≤ 43646199431503^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287247753 10000000000 43646199431503 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179501189/1000000000 : ℝ)^4427 ≤ (10705526060993/100000000000000 : ℝ)^3403 := by
    have hnat : (179501189 : ℕ)^4427*100000000000000^3403 ≤ 10705526060993^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179501189 1000000000 10705526060993 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547270697/1000000000 : ℝ)^4427 ≤ (9129654899427/20000000000000 : ℝ)^3403 := by
    have hnat : (547270697 : ℕ)^4427*20000000000000^3403 ≤ 9129654899427^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547270697 1000000000 9129654899427 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287247753/10000000000 : ℝ), (-179501189/1000000000 : ℝ), (547270697/1000000000 : ℝ)] ![(43646199431503/100000000000000 : ℝ), (10705526060993/100000000000000 : ℝ), (9129654899427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287247753/10000000000 : ℝ)|^4427 ≤ (43646199431503/100000000000000 : ℝ)^3403
        have hw : |(5287247753/10000000000 : ℝ)|=(5287247753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179501189/1000000000 : ℝ)|^4427 ≤ (10705526060993/100000000000000 : ℝ)^3403
        have hw : |(-179501189/1000000000 : ℝ)|=(179501189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547270697/1000000000 : ℝ)|^4427 ≤ (9129654899427/20000000000000 : ℝ)^3403
        have hw : |(547270697/1000000000 : ℝ)|=(547270697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s2_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321812021/2500000000 : ℝ)*x 0 + (5472706983/10000000000 : ℝ)*x 1 + (-1795011413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321812021/2500000000 : ℝ)^4427 ≤ (10911550746529/25000000000000 : ℝ)^3403 := by
    have hnat : (1321812021 : ℕ)^4427*25000000000000^3403 ≤ 10911550746529^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321812021 2500000000 10911550746529 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472706983/10000000000 : ℝ)^4427 ≤ (22824137319099/50000000000000 : ℝ)^3403 := by
    have hnat : (5472706983 : ℕ)^4427*50000000000000^3403 ≤ 22824137319099^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472706983 10000000000 22824137319099 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1795011413/10000000000 : ℝ)^4427 ≤ (10705522360099/100000000000000 : ℝ)^3403 := by
    have hnat : (1795011413 : ℕ)^4427*100000000000000^3403 ≤ 10705522360099^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795011413 10000000000 10705522360099 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321812021/2500000000 : ℝ), (5472706983/10000000000 : ℝ), (-1795011413/10000000000 : ℝ)] ![(10911550746529/25000000000000 : ℝ), (22824137319099/50000000000000 : ℝ), (10705522360099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321812021/2500000000 : ℝ)|^4427 ≤ (10911550746529/25000000000000 : ℝ)^3403
        have hw : |(1321812021/2500000000 : ℝ)|=(1321812021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472706983/10000000000 : ℝ)|^4427 ≤ (22824137319099/50000000000000 : ℝ)^3403
        have hw : |(5472706983/10000000000 : ℝ)|=(5472706983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1795011413/10000000000 : ℝ)|^4427 ≤ (10705522360099/100000000000000 : ℝ)^3403
        have hw : |(-1795011413/10000000000 : ℝ)|=(1795011413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s2_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4288528861/10000000000 : ℝ)*x 0 + (4613818777/10000000000 : ℝ)*x 1 + (995984357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288528861/10000000000 : ℝ)^4427 ≤ (6648074555117/20000000000000 : ℝ)^3403 := by
    have hnat : (4288528861 : ℕ)^4427*20000000000000^3403 ≤ 6648074555117^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288528861 10000000000 6648074555117 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4613818777/10000000000 : ℝ)^4427 ≤ (36557178061117/100000000000000 : ℝ)^3403 := by
    have hnat : (4613818777 : ℕ)^4427*100000000000000^3403 ≤ 36557178061117^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4613818777 10000000000 36557178061117 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995984357/2500000000 : ℝ)^4427 ≤ (15101224570863/50000000000000 : ℝ)^3403 := by
    have hnat : (995984357 : ℕ)^4427*50000000000000^3403 ≤ 15101224570863^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995984357 2500000000 15101224570863 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288528861/10000000000 : ℝ), (4613818777/10000000000 : ℝ), (995984357/2500000000 : ℝ)] ![(6648074555117/20000000000000 : ℝ), (36557178061117/100000000000000 : ℝ), (15101224570863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288528861/10000000000 : ℝ)|^4427 ≤ (6648074555117/20000000000000 : ℝ)^3403
        have hw : |(4288528861/10000000000 : ℝ)|=(4288528861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4613818777/10000000000 : ℝ)|^4427 ≤ (36557178061117/100000000000000 : ℝ)^3403
        have hw : |(4613818777/10000000000 : ℝ)|=(4613818777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995984357/2500000000 : ℝ)|^4427 ≤ (15101224570863/50000000000000 : ℝ)^3403
        have hw : |(995984357/2500000000 : ℝ)|=(995984357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (314/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4051/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7679/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7679/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7679/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7679/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (1524330895253303/100000000000000000000 : ℝ) := by
    have hpowers : (7679/100000 : ℝ)^4425 ≤ (1524330895253303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7679 : ℕ)^4425*100000000000000000000^1024 ≤ 1524330895253303^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7679 100000 1524330895253303 100000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7679/100000 : ℝ)) (X := (1524330895253303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18879/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (37176278894398811/50000000000000000000 : ℝ) := by
    have hpowers : (18879/100000 : ℝ)^4425 ≤ (37176278894398811/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18879 : ℕ)^4425*50000000000000000000^1024 ≤ 37176278894398811^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18879 100000 37176278894398811 50000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18879/100000 : ℝ)) (X := (37176278894398811/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001524330895253303/50000000000000000000 : ℝ) ≤ (2500017637249149/2500000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (50001524330895253303/50000000000000000000 : ℝ)^1024 ≤ (2500017637249149/2500000000000000 : ℝ)^4425 := by
      have hnat : (50001524330895253303 : ℕ)^1024*2500000000000000^4425 ≤ 2500017637249149^4425*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001524330895253303 50000000000000000000 2500017637249149 2500000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500017637249149/2500000000000000 : ℝ)) (X := (50001524330895253303/50000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4003035075547362037/4000000000000000000 : ℝ) ≤ (250043884343609/250000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (4003035075547362037/4000000000000000000 : ℝ)^1024 ≤ (250043884343609/250000000000000 : ℝ)^4425 := by
      have hnat : (4003035075547362037 : ℕ)^1024*250000000000000^4425 ≤ 250043884343609^4425*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4003035075547362037 4000000000000000000 250043884343609 250000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250043884343609/250000000000000 : ℝ)) (X := (4003035075547362037/4000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25037176278894398811/25000000000000000000 : ℝ) ≤ (2500860049623031/2500000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (25037176278894398811/25000000000000000000 : ℝ)^1024 ≤ (2500860049623031/2500000000000000 : ℝ)^4425 := by
      have hnat : (25037176278894398811 : ℕ)^1024*2500000000000000^4425 ≤ 2500860049623031^4425*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25037176278894398811 25000000000000000000 2500860049623031 2500000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500860049623031/2500000000000000 : ℝ)) (X := (25037176278894398811/25000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1524330895253303/100000000000000000000 : ℝ) ≤ ((1999552046612244923/2000000000000000000 : ℝ)+2*(421206186941/280000000000000 : ℝ)*(7679/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1999552046612244923/2000000000000000000 : ℝ)+2*(421206186941/280000000000000 : ℝ)*(7679/100000 : ℝ)=(2500017637249149/2500000000000000 : ℝ) by norm_num, show 1+2*(1524330895253303/100000000000000000000 : ℝ)=(50001524330895253303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37176278894398811/50000000000000000000 : ℝ)+(1524330895253303/100000000000000000000 : ℝ) ≤ ((1999552046612244923/2000000000000000000 : ℝ)+(421206186941/280000000000000 : ℝ)*((18879/100000 : ℝ)+(7679/100000 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (1999552046612244923/2000000000000000000 : ℝ)+(421206186941/280000000000000 : ℝ)*((18879/100000 : ℝ)+(7679/100000 : ℝ))=(250043884343609/250000000000000 : ℝ) by norm_num, show 1+(37176278894398811/50000000000000000000 : ℝ)+(1524330895253303/100000000000000000000 : ℝ)=(4003035075547362037/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37176278894398811/50000000000000000000 : ℝ) ≤ ((1999552046612244923/2000000000000000000 : ℝ)+2*(421206186941/280000000000000 : ℝ)*(18879/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1999552046612244923/2000000000000000000 : ℝ)+2*(421206186941/280000000000000 : ℝ)*(18879/100000 : ℝ)=(2500860049623031/2500000000000000 : ℝ) by norm_num, show 1+2*(37176278894398811/50000000000000000000 : ℝ)=(25037176278894398811/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1999552046612244923/2000000000000000000 : ℝ)*(X 1 0+X 2 0)+(421206186941/280000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (7679/100000 : ℝ)) (hi := (18879/100000 : ℝ)) (c := (1999552046612244923/2000000000000000000 : ℝ)) (alpha := (421206186941/280000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1999552046612244923/2000000000000000000 : ℝ)*(X 0 1+X 2 1)+(421206186941/280000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (7679/100000 : ℝ)) (hi := (18879/100000 : ℝ)) (c := (1999552046612244923/2000000000000000000 : ℝ)) (alpha := (421206186941/280000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1999552046612244923/2000000000000000000 : ℝ)*(X 0 2+X 1 2)+(421206186941/280000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (7679/100000 : ℝ)) (hi := (18879/100000 : ℝ)) (c := (1999552046612244923/2000000000000000000 : ℝ)) (alpha := (421206186941/280000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-386771249/2000000000 : ℝ)*X 0 0+(1368661741/2500000000 : ℝ)*X 0 1+(5183520993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2681558521/5000000000 : ℝ)*X 1 0+(-13026229/62500000 : ℝ)*X 1 1+(5183522343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536311797/1000000000 : ℝ)*X 2 0+(259176077/500000000 : ℝ)*X 2 1+(-2084196463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072095021/2500000000 : ℝ)*X 0 0+(994920973/2500000000 : ℝ)*X 0 1+(4618032833/10000000000 : ℝ)*X 0 2+(1072095021/2500000000 : ℝ)*X 1 0+(994920973/2500000000 : ℝ)*X 1 1+(4618032833/10000000000 : ℝ)*X 1 2+(1072095021/2500000000 : ℝ)*X 2 0+(994920973/2500000000 : ℝ)*X 2 1+(4618032833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1933923477/10000000000 : ℝ)*X 0 0+(1037088609/2000000000 : ℝ)*X 0 1+(547270689/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287247753/10000000000 : ℝ)*X 1 0+(-179501189/1000000000 : ℝ)*X 1 1+(547270697/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321812021/2500000000 : ℝ)*X 2 0+(5472706983/10000000000 : ℝ)*X 2 1+(-1795011413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4288528861/10000000000 : ℝ)*X 0 0+(4613818777/10000000000 : ℝ)*X 0 1+(995984357/2500000000 : ℝ)*X 0 2+(4288528861/10000000000 : ℝ)*X 1 0+(4613818777/10000000000 : ℝ)*X 1 1+(995984357/2500000000 : ℝ)*X 1 2+(4288528861/10000000000 : ℝ)*X 2 0+(4613818777/10000000000 : ℝ)*X 2 1+(995984357/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (972526592767711949076632517/100000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1556329183/100000000000000 : ℝ)*(base19) + (1914274201/100000000000000 : ℝ)*(base23) + (93806311/50000000000000 : ℝ)*(upper3) + (7924879/6250000000000 : ℝ)*(upper4) + (16033651/6250000000000 : ℝ)*(upper5) + (2500786269371093/100000000000000 : ℝ)*(major0) + (2500786269371093/100000000000000 : ℝ)*(major1) + (2500786269371093/100000000000000 : ℝ)*(major2) + (429371030526309/12500000000000 : ℝ)*(sp0) + (1717501078473397/50000000000000 : ℝ)*(sp1) + (214687612437611/6250000000000 : ℝ)*(sp2) + (78327715076443/5000000000000 : ℝ)*(sp3) + (7093813101/20000000000000 : ℝ)*(sp4) + (7099880907/50000000000000 : ℝ)*(sp7) + (783284250645337/50000000000000 : ℝ)*(f.failure) + (429375464159497/12500000000000 : ℝ)*(f.sum) + (22008945530513/14000000000000000000000000000 : ℝ)*base65 + (505586792071125873/1400000000000000000000000000000000 : ℝ)*base67 + (609553229728874127/1400000000000000000000000000000000 : ℝ)*base70 + (3922651163328874127/1400000000000000000000000000000000 : ℝ)*base72 + (4091994635487/14000000000000000000000000000 : ℝ)*base74 + (8959083504128874127/1400000000000000000000000000000000 : ℝ)*base76 + (8597043084128874127/1400000000000000000000000000000000 : ℝ)*base78 + (882487362271125873/1400000000000000000000000000000000 : ℝ)*base79 + (26363828720513/14000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (644873/2500000000000000000000 : ℝ)*base89 + (644873/2500000000000000000000 : ℝ)*base91 + (644873/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2033240745649218633159850587/350000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (507021757/100000000000000 : ℝ)*(base19) + (236891239/25000000000000 : ℝ)*(base23) + (57306607/50000000000000 : ℝ)*(upper3) + (30508199/50000000000000 : ℝ)*(lower4) + (129773751/100000000000000 : ℝ)*(upper5) + (1267180560731137/50000000000000 : ℝ)*(major0) + (1267180560731137/50000000000000 : ℝ)*(major1) + (1267180560731137/50000000000000 : ℝ)*(major2) + (2468654079/50000000000000 : ℝ)*(sp1) + (6204281711/50000000000000 : ℝ)*(sp2) + (1740560620263469/50000000000000 : ℝ)*(sp4) + (3481115796197023/100000000000000 : ℝ)*(sp5) + (21756924277491/625000000000 : ℝ)*(sp6) + (1587600808755623/100000000000000 : ℝ)*(sp7) + (1587600808755623/100000000000000 : ℝ)*(f.failure) + (1740560620263469/50000000000000 : ℝ)*(f.sum) + (30117977642917/7000000000000000000000000000 : ℝ)*base65 + (5953495213969722157/700000000000000000000000000000000 : ℝ)*base67 + (6351598385869722157/700000000000000000000000000000000 : ℝ)*base69 + (2572058360069722157/700000000000000000000000000000000 : ℝ)*base71 + (20993278114917/7000000000000000000000000000 : ℝ)*base73 + (953673207069722157/700000000000000000000000000000000 : ℝ)*base75 + (9090609262569722157/700000000000000000000000000000000 : ℝ)*base77 + (4782389508969722157/700000000000000000000000000000000 : ℝ)*base79 + (28659149635917/7000000000000000000000000000 : ℝ)*base81 + (58409033/5000000000000000000000 : ℝ)*base90 + (58409033/5000000000000000000000 : ℝ)*base92 + (58409033/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1465_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7679/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4051/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1465_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1465_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4051/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1465_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1465_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1465_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (314/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4051/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1465_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
