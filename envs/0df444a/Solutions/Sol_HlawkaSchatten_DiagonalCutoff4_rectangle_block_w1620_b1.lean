-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1620_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:54:23.337853+00:00
-- url     : https://prove2.me/submissions/304382ac-f028-40d6-9ee5-75a6fc85c178

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
theorem support_rectangle_w1620_s3_0 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-839672773/5000000000 : ℝ)*x 0 + (1364204901/2500000000 : ℝ)*x 1 + (5181364207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839672773/5000000000 : ℝ)^4799 ≤ (10350298989833/100000000000000 : ℝ)^3775 := by
    have hnat : (839672773 : ℕ)^4799*100000000000000^3775 ≤ 10350298989833^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839672773 5000000000 10350298989833 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364204901/2500000000 : ℝ)^4799 ≤ (1446879310067/3125000000000 : ℝ)^3775 := by
    have hnat : (1364204901 : ℕ)^4799*3125000000000^3775 ≤ 1446879310067^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364204901 2500000000 1446879310067 3125000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181364207/10000000000 : ℝ)^4799 ≤ (2709347692131/6250000000000 : ℝ)^3775 := by
    have hnat : (5181364207 : ℕ)^4799*6250000000000^3775 ≤ 2709347692131^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181364207 10000000000 2709347692131 6250000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-839672773/5000000000 : ℝ), (1364204901/2500000000 : ℝ), (5181364207/10000000000 : ℝ)] ![(10350298989833/100000000000000 : ℝ), (1446879310067/3125000000000 : ℝ), (2709347692131/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-839672773/5000000000 : ℝ)|^4799 ≤ (10350298989833/100000000000000 : ℝ)^3775
        have hw : |(-839672773/5000000000 : ℝ)|=(839672773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364204901/2500000000 : ℝ)|^4799 ≤ (1446879310067/3125000000000 : ℝ)^3775
        have hw : |(1364204901/2500000000 : ℝ)|=(1364204901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181364207/10000000000 : ℝ)|^4799 ≤ (2709347692131/6250000000000 : ℝ)^3775
        have hw : |(5181364207/10000000000 : ℝ)|=(5181364207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s3_1 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676124519/5000000000 : ℝ)*x 0 + (-364266559/2000000000 : ℝ)*x 1 + (2590682123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676124519/5000000000 : ℝ)^4799 ≤ (2823446466281/6250000000000 : ℝ)^3775 := by
    have hnat : (2676124519 : ℕ)^4799*6250000000000^3775 ≤ 2823446466281^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676124519 5000000000 2823446466281 6250000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364266559/2000000000 : ℝ)^4799 ≤ (11475293037643/100000000000000 : ℝ)^3775 := by
    have hnat : (364266559 : ℕ)^4799*100000000000000^3775 ≤ 11475293037643^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364266559 2000000000 11475293037643 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590682123/5000000000 : ℝ)^4799 ≤ (338668464757/781250000000 : ℝ)^3775 := by
    have hnat : (2590682123 : ℕ)^4799*781250000000^3775 ≤ 338668464757^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590682123 5000000000 338668464757 781250000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676124519/5000000000 : ℝ), (-364266559/2000000000 : ℝ), (2590682123/5000000000 : ℝ)] ![(2823446466281/6250000000000 : ℝ), (11475293037643/100000000000000 : ℝ), (338668464757/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676124519/5000000000 : ℝ)|^4799 ≤ (2823446466281/6250000000000 : ℝ)^3775
        have hw : |(2676124519/5000000000 : ℝ)|=(2676124519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-364266559/2000000000 : ℝ)|^4799 ≤ (11475293037643/100000000000000 : ℝ)^3775
        have hw : |(-364266559/2000000000 : ℝ)|=(364266559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590682123/5000000000 : ℝ)|^4799 ≤ (338668464757/781250000000 : ℝ)^3775
        have hw : |(2590682123/5000000000 : ℝ)|=(2590682123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s3_2 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676124517/5000000000 : ℝ)*x 0 + (2590682123/5000000000 : ℝ)*x 1 + (-1138333/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676124517/5000000000 : ℝ)^4799 ≤ (5646892927197/12500000000000 : ℝ)^3775 := by
    have hnat : (2676124517 : ℕ)^4799*12500000000000^3775 ≤ 5646892927197^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676124517 5000000000 5646892927197 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590682123/5000000000 : ℝ)^4799 ≤ (338668464757/781250000000 : ℝ)^3775 := by
    have hnat : (2590682123 : ℕ)^4799*781250000000^3775 ≤ 338668464757^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590682123 5000000000 338668464757 781250000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138333/6250000 : ℝ)^4799 ≤ (11475293077691/100000000000000 : ℝ)^3775 := by
    have hnat : (1138333 : ℕ)^4799*100000000000000^3775 ≤ 11475293077691^3775*6250000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138333 6250000 11475293077691 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676124517/5000000000 : ℝ), (2590682123/5000000000 : ℝ), (-1138333/6250000 : ℝ)] ![(5646892927197/12500000000000 : ℝ), (338668464757/781250000000 : ℝ), (11475293077691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676124517/5000000000 : ℝ)|^4799 ≤ (5646892927197/12500000000000 : ℝ)^3775
        have hw : |(2676124517/5000000000 : ℝ)|=(2676124517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590682123/5000000000 : ℝ)|^4799 ≤ (338668464757/781250000000 : ℝ)^3775
        have hw : |(2590682123/5000000000 : ℝ)|=(2590682123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1138333/6250000 : ℝ)|^4799 ≤ (11475293077691/100000000000000 : ℝ)^3775
        have hw : |(-1138333/6250000 : ℝ)|=(1138333/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s3_3 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131385001/312500000 : ℝ)*x 0 + (3872020631/10000000000 : ℝ)*x 1 + (455782977/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131385001/312500000 : ℝ)^4799 ≤ (33236870788119/100000000000000 : ℝ)^3775 := by
    have hnat : (131385001 : ℕ)^4799*100000000000000^3775 ≤ 33236870788119^3775*312500000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131385001 312500000 33236870788119 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3872020631/10000000000 : ℝ)^4799 ≤ (29933833767371/100000000000000 : ℝ)^3775 := by
    have hnat : (3872020631 : ℕ)^4799*100000000000000^3775 ≤ 29933833767371^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872020631 10000000000 29933833767371 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455782977/1000000000 : ℝ)^4799 ≤ (36829295439317/100000000000000 : ℝ)^3775 := by
    have hnat : (455782977 : ℕ)^4799*100000000000000^3775 ≤ 36829295439317^3775*1000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455782977 1000000000 36829295439317 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131385001/312500000 : ℝ), (3872020631/10000000000 : ℝ), (455782977/1000000000 : ℝ)] ![(33236870788119/100000000000000 : ℝ), (29933833767371/100000000000000 : ℝ), (36829295439317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131385001/312500000 : ℝ)|^4799 ≤ (33236870788119/100000000000000 : ℝ)^3775
        have hw : |(131385001/312500000 : ℝ)|=(131385001/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3872020631/10000000000 : ℝ)|^4799 ≤ (29933833767371/100000000000000 : ℝ)^3775
        have hw : |(3872020631/10000000000 : ℝ)|=(3872020631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(455782977/1000000000 : ℝ)|^4799 ≤ (36829295439317/100000000000000 : ℝ)^3775
        have hw : |(455782977/1000000000 : ℝ)|=(455782977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s3_4 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-167941483/1000000000 : ℝ)*x 0 + (5183426177/10000000000 : ℝ)*x 1 + (2727367929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167941483/1000000000 : ℝ)^4799 ≤ (5175420921269/50000000000000 : ℝ)^3775 := by
    have hnat : (167941483 : ℕ)^4799*50000000000000^3775 ≤ 5175420921269^3775*1000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167941483 1000000000 5175420921269 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183426177/10000000000 : ℝ)^4799 ≤ (43371495172119/100000000000000 : ℝ)^3775 := by
    have hnat : (5183426177 : ℕ)^4799*100000000000000^3775 ≤ 43371495172119^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183426177 10000000000 43371495172119 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727367929/5000000000 : ℝ)^4799 ≤ (46277662970517/100000000000000 : ℝ)^3775 := by
    have hnat : (2727367929 : ℕ)^4799*100000000000000^3775 ≤ 46277662970517^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727367929 5000000000 46277662970517 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167941483/1000000000 : ℝ), (5183426177/10000000000 : ℝ), (2727367929/5000000000 : ℝ)] ![(5175420921269/50000000000000 : ℝ), (43371495172119/100000000000000 : ℝ), (46277662970517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167941483/1000000000 : ℝ)|^4799 ≤ (5175420921269/50000000000000 : ℝ)^3775
        have hw : |(-167941483/1000000000 : ℝ)|=(167941483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183426177/10000000000 : ℝ)|^4799 ≤ (43371495172119/100000000000000 : ℝ)^3775
        have hw : |(5183426177/10000000000 : ℝ)|=(5183426177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727367929/5000000000 : ℝ)|^4799 ≤ (46277662970517/100000000000000 : ℝ)^3775
        have hw : |(2727367929/5000000000 : ℝ)|=(2727367929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s3_5 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278968649/10000000000 : ℝ)*x 0 + (-30959223/200000000 : ℝ)*x 1 + (5454735857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278968649/10000000000 : ℝ)^4799 ≤ (44390314783043/100000000000000 : ℝ)^3775 := by
    have hnat : (5278968649 : ℕ)^4799*100000000000000^3775 ≤ 44390314783043^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278968649 10000000000 44390314783043 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30959223/200000000 : ℝ)^4799 ≤ (2333005558649/25000000000000 : ℝ)^3775 := by
    have hnat : (30959223 : ℕ)^4799*25000000000000^3775 ≤ 2333005558649^3775*200000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30959223 200000000 2333005558649 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454735857/10000000000 : ℝ)^4799 ≤ (46277662959731/100000000000000 : ℝ)^3775 := by
    have hnat : (5454735857 : ℕ)^4799*100000000000000^3775 ≤ 46277662959731^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454735857 10000000000 46277662959731 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278968649/10000000000 : ℝ), (-30959223/200000000 : ℝ), (5454735857/10000000000 : ℝ)] ![(44390314783043/100000000000000 : ℝ), (2333005558649/25000000000000 : ℝ), (46277662959731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278968649/10000000000 : ℝ)|^4799 ≤ (44390314783043/100000000000000 : ℝ)^3775
        have hw : |(5278968649/10000000000 : ℝ)|=(5278968649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30959223/200000000 : ℝ)|^4799 ≤ (2333005558649/25000000000000 : ℝ)^3775
        have hw : |(-30959223/200000000 : ℝ)|=(30959223/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454735857/10000000000 : ℝ)|^4799 ≤ (46277662959731/100000000000000 : ℝ)^3775
        have hw : |(5454735857/10000000000 : ℝ)|=(5454735857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s3_6 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278968647/10000000000 : ℝ)*x 0 + (2727367931/5000000000 : ℝ)*x 1 + (-1547961147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278968647/10000000000 : ℝ)^4799 ≤ (44390314761663/100000000000000 : ℝ)^3775 := by
    have hnat : (5278968647 : ℕ)^4799*100000000000000^3775 ≤ 44390314761663^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278968647 10000000000 44390314761663 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727367931/5000000000 : ℝ)^4799 ≤ (23138831506829/50000000000000 : ℝ)^3775 := by
    have hnat : (2727367931 : ℕ)^4799*50000000000000^3775 ≤ 23138831506829^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727367931 5000000000 23138831506829 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1547961147/10000000000 : ℝ)^4799 ≤ (2333005552901/25000000000000 : ℝ)^3775 := by
    have hnat : (1547961147 : ℕ)^4799*25000000000000^3775 ≤ 2333005552901^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1547961147 10000000000 2333005552901 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278968647/10000000000 : ℝ), (2727367931/5000000000 : ℝ), (-1547961147/10000000000 : ℝ)] ![(44390314761663/100000000000000 : ℝ), (23138831506829/50000000000000 : ℝ), (2333005552901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278968647/10000000000 : ℝ)|^4799 ≤ (44390314761663/100000000000000 : ℝ)^3775
        have hw : |(5278968647/10000000000 : ℝ)|=(5278968647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727367931/5000000000 : ℝ)|^4799 ≤ (23138831506829/50000000000000 : ℝ)^3775
        have hw : |(2727367931/5000000000 : ℝ)|=(2727367931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1547961147/10000000000 : ℝ)|^4799 ≤ (2333005552901/25000000000000 : ℝ)^3775
        have hw : |(-1547961147/10000000000 : ℝ)|=(1547961147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s3_7 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102246237/5000000000 : ℝ)*x 0 + (1138174013/2500000000 : ℝ)*x 1 + (3877208431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102246237/5000000000 : ℝ)^4799 ≤ (33238603808311/100000000000000 : ℝ)^3775 := by
    have hnat : (2102246237 : ℕ)^4799*100000000000000^3775 ≤ 33238603808311^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102246237 5000000000 33238603808311 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138174013/2500000000 : ℝ)^4799 ≤ (36776568235111/100000000000000 : ℝ)^3775 := by
    have hnat : (1138174013 : ℕ)^4799*100000000000000^3775 ≤ 36776568235111^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138174013 2500000000 36776568235111 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3877208431/10000000000 : ℝ)^4799 ≤ (14992413972069/50000000000000 : ℝ)^3775 := by
    have hnat : (3877208431 : ℕ)^4799*50000000000000^3775 ≤ 14992413972069^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3877208431 10000000000 14992413972069 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102246237/5000000000 : ℝ), (1138174013/2500000000 : ℝ), (3877208431/10000000000 : ℝ)] ![(33238603808311/100000000000000 : ℝ), (36776568235111/100000000000000 : ℝ), (14992413972069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102246237/5000000000 : ℝ)|^4799 ≤ (33238603808311/100000000000000 : ℝ)^3775
        have hw : |(2102246237/5000000000 : ℝ)|=(2102246237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1138174013/2500000000 : ℝ)|^4799 ≤ (36776568235111/100000000000000 : ℝ)^3775
        have hw : |(1138174013/2500000000 : ℝ)|=(1138174013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3877208431/10000000000 : ℝ)|^4799 ≤ (14992413972069/50000000000000 : ℝ)^3775
        have hw : |(3877208431/10000000000 : ℝ)|=(3877208431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1620_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1049/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8167/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16453/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16453/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16453/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16453/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16453/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16453/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10383/100000 : ℝ) ^ (4795/1024 : ℝ) ≤ (2476375446290409/100000000000000000000 : ℝ) := by
    have hpowers : (10383/100000 : ℝ)^4795 ≤ (2476375446290409/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10383 : ℕ)^4795*100000000000000000000^1024 ≤ 2476375446290409^1024*100000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10383 100000 2476375446290409 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10383/100000 : ℝ)) (X := (2476375446290409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16453/100000 : ℝ) ^ (4795/1024 : ℝ) ≤ (21378430769141409/100000000000000000000 : ℝ) := by
    have hpowers : (16453/100000 : ℝ)^4795 ≤ (21378430769141409/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16453 : ℕ)^4795*100000000000000000000^1024 ≤ 21378430769141409^1024*100000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16453 100000 21378430769141409 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16453/100000 : ℝ)) (X := (21378430769141409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002476375446290409/50000000000000000000 : ℝ) ≤ (5000052883400893/5000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50002476375446290409/50000000000000000000 : ℝ)^1024 ≤ (5000052883400893/5000000000000000 : ℝ)^4795 := by
      have hnat : (50002476375446290409 : ℕ)^1024*5000000000000000^4795 ≤ 5000052883400893^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002476375446290409 50000000000000000000 5000052883400893 5000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000052883400893/5000000000000000 : ℝ)) (X := (50002476375446290409/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011927403107715909/50000000000000000000 : ℝ) ≤ (10000509385412917/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50011927403107715909/50000000000000000000 : ℝ)^1024 ≤ (10000509385412917/10000000000000000 : ℝ)^4795 := by
      have hnat : (50011927403107715909 : ℕ)^1024*10000000000000000^4795 ≤ 10000509385412917^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011927403107715909 50000000000000000000 10000509385412917 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000509385412917/10000000000000000 : ℝ)) (X := (50011927403107715909/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021378430769141409/50000000000000000000 : ℝ) ≤ (625057062751503/625000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50021378430769141409/50000000000000000000 : ℝ)^1024 ≤ (625057062751503/625000000000000 : ℝ)^4795 := by
      have hnat : (50021378430769141409 : ℕ)^1024*625000000000000^4795 ≤ 625057062751503^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021378430769141409 50000000000000000000 625057062751503 625000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625057062751503/625000000000000 : ℝ)) (X := (50021378430769141409/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2476375446290409/100000000000000000000 : ℝ) ≤ ((30346130230204047337/30350000000000000000 : ℝ)+2*(403618611131/607000000000000 : ℝ)*(10383/100000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (30346130230204047337/30350000000000000000 : ℝ)+2*(403618611131/607000000000000 : ℝ)*(10383/100000 : ℝ)=(5000052883400893/5000000000000000 : ℝ) by norm_num, show 1+2*(2476375446290409/100000000000000000000 : ℝ)=(50002476375446290409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21378430769141409/100000000000000000000 : ℝ)+(2476375446290409/100000000000000000000 : ℝ) ≤ ((30346130230204047337/30350000000000000000 : ℝ)+(403618611131/607000000000000 : ℝ)*((16453/100000 : ℝ)+(10383/100000 : ℝ)))^(4795/1024 : ℝ) := by
    rw [show (30346130230204047337/30350000000000000000 : ℝ)+(403618611131/607000000000000 : ℝ)*((16453/100000 : ℝ)+(10383/100000 : ℝ))=(10000509385412917/10000000000000000 : ℝ) by norm_num, show 1+(21378430769141409/100000000000000000000 : ℝ)+(2476375446290409/100000000000000000000 : ℝ)=(50011927403107715909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21378430769141409/100000000000000000000 : ℝ) ≤ ((30346130230204047337/30350000000000000000 : ℝ)+2*(403618611131/607000000000000 : ℝ)*(16453/100000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (30346130230204047337/30350000000000000000 : ℝ)+2*(403618611131/607000000000000 : ℝ)*(16453/100000 : ℝ)=(625057062751503/625000000000000 : ℝ) by norm_num, show 1+2*(21378430769141409/100000000000000000000 : ℝ)=(50021378430769141409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30346130230204047337/30350000000000000000 : ℝ)*(X 1 0+X 2 0)+(403618611131/607000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (16453/100000 : ℝ)) (c := (30346130230204047337/30350000000000000000 : ℝ)) (alpha := (403618611131/607000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30346130230204047337/30350000000000000000 : ℝ)*(X 0 1+X 2 1)+(403618611131/607000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (16453/100000 : ℝ)) (c := (30346130230204047337/30350000000000000000 : ℝ)) (alpha := (403618611131/607000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30346130230204047337/30350000000000000000 : ℝ)*(X 0 2+X 1 2)+(403618611131/607000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (10383/100000 : ℝ)) (hi := (16453/100000 : ℝ)) (c := (30346130230204047337/30350000000000000000 : ℝ)) (alpha := (403618611131/607000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-839672773/5000000000 : ℝ)*X 0 0+(1364204901/2500000000 : ℝ)*X 0 1+(5181364207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676124519/5000000000 : ℝ)*X 1 0+(-364266559/2000000000 : ℝ)*X 1 1+(2590682123/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676124517/5000000000 : ℝ)*X 2 0+(2590682123/5000000000 : ℝ)*X 2 1+(-1138333/6250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((131385001/312500000 : ℝ)*X 0 0+(3872020631/10000000000 : ℝ)*X 0 1+(455782977/1000000000 : ℝ)*X 0 2+(131385001/312500000 : ℝ)*X 1 0+(3872020631/10000000000 : ℝ)*X 1 1+(455782977/1000000000 : ℝ)*X 1 2+(131385001/312500000 : ℝ)*X 2 0+(3872020631/10000000000 : ℝ)*X 2 1+(455782977/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-167941483/1000000000 : ℝ)*X 0 0+(5183426177/10000000000 : ℝ)*X 0 1+(2727367929/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278968649/10000000000 : ℝ)*X 1 0+(-30959223/200000000 : ℝ)*X 1 1+(5454735857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278968647/10000000000 : ℝ)*X 2 0+(2727367931/5000000000 : ℝ)*X 2 1+(-1547961147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102246237/5000000000 : ℝ)*X 0 0+(1138174013/2500000000 : ℝ)*X 0 1+(3877208431/10000000000 : ℝ)*X 0 2+(2102246237/5000000000 : ℝ)*X 1 0+(1138174013/2500000000 : ℝ)*X 1 1+(3877208431/10000000000 : ℝ)*X 1 2+(2102246237/5000000000 : ℝ)*X 2 0+(1138174013/2500000000 : ℝ)*X 2 1+(3877208431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14290163932498741015453277883/1517500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (292074779/20000000000000 : ℝ)*(base19) + (1345023529/100000000000000 : ℝ)*(base23) + (30143117/50000000000000 : ℝ)*(lower2) + (227664561/100000000000000 : ℝ)*(upper3) + (141308433/100000000000000 : ℝ)*(upper5) + (2544267498389451/100000000000000 : ℝ)*(major0) + (2544267498389451/100000000000000 : ℝ)*(major1) + (2544267498389451/100000000000000 : ℝ)*(major2) + (3630370592104169/100000000000000 : ℝ)*(sp0) + (726077412635557/20000000000000 : ℝ)*(sp1) + (3630387178528151/100000000000000 : ℝ)*(sp2) + (1458138374558587/100000000000000 : ℝ)*(sp3) + (17931447511/100000000000000 : ℝ)*(sp4) + (3892385783/50000000000000 : ℝ)*(sp7) + (1458146159330153/100000000000000 : ℝ)*(f.failure) + (11344964136099/312500000000 : ℝ)*(f.sum) + (177072862776681/30350000000000000000000000000 : ℝ)*base65 + (4274035890100508013/3035000000000000000000000000000000 : ℝ)*base68 + (18497096015275508013/3035000000000000000000000000000000 : ℝ)*base70 + (11308375412210508013/3035000000000000000000000000000000 : ℝ)*base72 + (25560948404819/30350000000000000000000000000 : ℝ)*base74 + (6878650716390508013/3035000000000000000000000000000000 : ℝ)*base76 + (1421363059850508013/3035000000000000000000000000000000 : ℝ)*base78 + (14798398020905508013/3035000000000000000000000000000000 : ℝ)*base80 + (19780483201481/30350000000000000000000000000 : ℝ)*base81 + (1603211/2500000000000000000000 : ℝ)*base90 + (1603211/2500000000000000000000 : ℝ)*base92 + (1603211/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4223714107998779805903/474218750000000000000000000 : ℝ) := by norm_num
    linear_combination (1359389401/100000000000000 : ℝ)*(base19) + (1468896331/100000000000000 : ℝ)*(base23) + (37841447/20000000000000 : ℝ)*(upper3) + (24594997/50000000000000 : ℝ)*(lower4) + (36588217/20000000000000 : ℝ)*(upper5) + (1291559076132347/50000000000000 : ℝ)*(major0) + (1291559076132347/50000000000000 : ℝ)*(major1) + (1291559076132347/50000000000000 : ℝ)*(major2) + (15667412287/100000000000000 : ℝ)*(sp1) + (16944089381/100000000000000 : ℝ)*(sp2) + (3685824134594099/100000000000000 : ℝ)*(sp4) + (3685807107792411/100000000000000 : ℝ)*(sp5) + (3685805721608387/100000000000000 : ℝ)*(sp6) + (1480411873045991/100000000000000 : ℝ)*(sp7) + (1480411873045991/100000000000000 : ℝ)*(f.failure) + (3685824134594099/100000000000000 : ℝ)*(f.sum) + (12346280270757/15175000000000000000000000000 : ℝ)*base65 + (3672075367574740061/1517500000000000000000000000000000 : ℝ)*base68 + (8141408792214740061/1517500000000000000000000000000000 : ℝ)*base70 + (2081271968255259939/1517500000000000000000000000000000 : ℝ)*base71 + (40292399938009/7587500000000000000000000000 : ℝ)*base74 + (7782371404262759939/1517500000000000000000000000000000 : ℝ)*base75 + (4804987788459740061/1517500000000000000000000000000000 : ℝ)*base78 + (7551025642977759939/1517500000000000000000000000000000 : ℝ)*base79 + (49254050476143/15175000000000000000000000000 : ℝ)*base82 + (603483/2500000000000000000000 : ℝ)*base89 + (603483/2500000000000000000000 : ℝ)*base91 + (603483/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1620_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1049/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8167/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1620_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1620_s4_0 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419859387/2500000000 : ℝ)*x 0 + (682044649/1250000000 : ℝ)*x 1 + (20241271/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419859387/2500000000 : ℝ)^4799 ≤ (1035101984351/10000000000000 : ℝ)^3775 := by
    have hnat : (419859387 : ℕ)^4799*10000000000000^3775 ≤ 1035101984351^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419859387 2500000000 1035101984351 10000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682044649/1250000000 : ℝ)^4799 ≤ (5786893777391/12500000000000 : ℝ)^3775 := by
    have hnat : (682044649 : ℕ)^4799*12500000000000^3775 ≤ 5786893777391^3775*1250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682044649 1250000000 5786893777391 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20241271/39062500 : ℝ)^4799 ≤ (21676914956883/50000000000000 : ℝ)^3775 := by
    have hnat : (20241271 : ℕ)^4799*50000000000000^3775 ≤ 21676914956883^3775*39062500^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20241271 39062500 21676914956883 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419859387/2500000000 : ℝ), (682044649/1250000000 : ℝ), (20241271/39062500 : ℝ)] ![(1035101984351/10000000000000 : ℝ), (5786893777391/12500000000000 : ℝ), (21676914956883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419859387/2500000000 : ℝ)|^4799 ≤ (1035101984351/10000000000000 : ℝ)^3775
        have hw : |(-419859387/2500000000 : ℝ)|=(419859387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682044649/1250000000 : ℝ)|^4799 ≤ (5786893777391/12500000000000 : ℝ)^3775
        have hw : |(682044649/1250000000 : ℝ)|=(682044649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20241271/39062500 : ℝ)|^4799 ≤ (21676914956883/50000000000000 : ℝ)^3775
        have hw : |(20241271/39062500 : ℝ)|=(20241271/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s4_1 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352124963/10000000000 : ℝ)*x 0 + (-455241587/2500000000 : ℝ)*x 1 + (1036353073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352124963/10000000000 : ℝ)^4799 ≤ (4517381214821/10000000000000 : ℝ)^3775 := by
    have hnat : (5352124963 : ℕ)^4799*10000000000000^3775 ≤ 4517381214821^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352124963 10000000000 4517381214821 10000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455241587/2500000000 : ℝ)^4799 ≤ (11472358041129/100000000000000 : ℝ)^3775 := by
    have hnat : (455241587 : ℕ)^4799*100000000000000^3775 ≤ 11472358041129^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455241587 2500000000 11472358041129 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036353073/2000000000 : ℝ)^4799 ≤ (1354807181149/3125000000000 : ℝ)^3775 := by
    have hnat : (1036353073 : ℕ)^4799*3125000000000^3775 ≤ 1354807181149^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036353073 2000000000 1354807181149 3125000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352124963/10000000000 : ℝ), (-455241587/2500000000 : ℝ), (1036353073/2000000000 : ℝ)] ![(4517381214821/10000000000000 : ℝ), (11472358041129/100000000000000 : ℝ), (1354807181149/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352124963/10000000000 : ℝ)|^4799 ≤ (4517381214821/10000000000000 : ℝ)^3775
        have hw : |(5352124963/10000000000 : ℝ)|=(5352124963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-455241587/2500000000 : ℝ)|^4799 ≤ (11472358041129/100000000000000 : ℝ)^3775
        have hw : |(-455241587/2500000000 : ℝ)|=(455241587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036353073/2000000000 : ℝ)|^4799 ≤ (1354807181149/3125000000000 : ℝ)^3775
        have hw : |(1036353073/2000000000 : ℝ)|=(1036353073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s4_2 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676062481/5000000000 : ℝ)*x 0 + (518176537/1000000000 : ℝ)*x 1 + (-910483171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676062481/5000000000 : ℝ)^4799 ≤ (1129345303437/2500000000000 : ℝ)^3775 := by
    have hnat : (2676062481 : ℕ)^4799*2500000000000^3775 ≤ 1129345303437^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676062481 5000000000 1129345303437 2500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518176537/1000000000 : ℝ)^4799 ≤ (43353829849949/100000000000000 : ℝ)^3775 := by
    have hnat : (518176537 : ℕ)^4799*100000000000000^3775 ≤ 43353829849949^3775*1000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518176537 1000000000 43353829849949 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910483171/5000000000 : ℝ)^4799 ≤ (5736178996537/50000000000000 : ℝ)^3775 := by
    have hnat : (910483171 : ℕ)^4799*50000000000000^3775 ≤ 5736178996537^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910483171 5000000000 5736178996537 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676062481/5000000000 : ℝ), (518176537/1000000000 : ℝ), (-910483171/5000000000 : ℝ)] ![(1129345303437/2500000000000 : ℝ), (43353829849949/100000000000000 : ℝ), (5736178996537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676062481/5000000000 : ℝ)|^4799 ≤ (1129345303437/2500000000000 : ℝ)^3775
        have hw : |(2676062481/5000000000 : ℝ)|=(2676062481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518176537/1000000000 : ℝ)|^4799 ≤ (43353829849949/100000000000000 : ℝ)^3775
        have hw : |(518176537/1000000000 : ℝ)|=(518176537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-910483171/5000000000 : ℝ)|^4799 ≤ (5736178996537/50000000000000 : ℝ)^3775
        have hw : |(-910483171/5000000000 : ℝ)|=(910483171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s4_3 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (840876029/2000000000 : ℝ)*x 0 + (3873089257/10000000000 : ℝ)*x 1 + (4556748499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840876029/2000000000 : ℝ)^4799 ≤ (33237474913943/100000000000000 : ℝ)^3775 := by
    have hnat : (840876029 : ℕ)^4799*100000000000000^3775 ≤ 33237474913943^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840876029 2000000000 33237474913943 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3873089257/10000000000 : ℝ)^4799 ≤ (29944336455399/100000000000000 : ℝ)^3775 := by
    have hnat : (3873089257 : ℕ)^4799*100000000000000^3775 ≤ 29944336455399^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3873089257 10000000000 29944336455399 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556748499/10000000000 : ℝ)^4799 ≤ (36818188620577/100000000000000 : ℝ)^3775 := by
    have hnat : (4556748499 : ℕ)^4799*100000000000000^3775 ≤ 36818188620577^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556748499 10000000000 36818188620577 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840876029/2000000000 : ℝ), (3873089257/10000000000 : ℝ), (4556748499/10000000000 : ℝ)] ![(33237474913943/100000000000000 : ℝ), (29944336455399/100000000000000 : ℝ), (36818188620577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840876029/2000000000 : ℝ)|^4799 ≤ (33237474913943/100000000000000 : ℝ)^3775
        have hw : |(840876029/2000000000 : ℝ)|=(840876029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3873089257/10000000000 : ℝ)|^4799 ≤ (29944336455399/100000000000000 : ℝ)^3775
        have hw : |(3873089257/10000000000 : ℝ)|=(3873089257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556748499/10000000000 : ℝ)|^4799 ≤ (36818188620577/100000000000000 : ℝ)^3775
        have hw : |(4556748499/10000000000 : ℝ)|=(4556748499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s4_4 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1679506157/10000000000 : ℝ)*x 0 + (40498551/78125000 : ℝ)*x 1 + (681785811/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1679506157/10000000000 : ℝ)^4799 ≤ (5175778707713/50000000000000 : ℝ)^3775 := by
    have hnat : (1679506157 : ℕ)^4799*50000000000000^3775 ≤ 5175778707713^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679506157 10000000000 5175778707713 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40498551/78125000 : ℝ)^4799 ≤ (43375626123763/100000000000000 : ℝ)^3775 := by
    have hnat : (40498551 : ℕ)^4799*100000000000000^3775 ≤ 43375626123763^3775*78125000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40498551 78125000 43375626123763 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681785811/1250000000 : ℝ)^4799 ≤ (46272816442689/100000000000000 : ℝ)^3775 := by
    have hnat : (681785811 : ℕ)^4799*100000000000000^3775 ≤ 46272816442689^3775*1250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681785811 1250000000 46272816442689 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1679506157/10000000000 : ℝ), (40498551/78125000 : ℝ), (681785811/1250000000 : ℝ)] ![(5175778707713/50000000000000 : ℝ), (43375626123763/100000000000000 : ℝ), (46272816442689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1679506157/10000000000 : ℝ)|^4799 ≤ (5175778707713/50000000000000 : ℝ)^3775
        have hw : |(-1679506157/10000000000 : ℝ)|=(1679506157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40498551/78125000 : ℝ)|^4799 ≤ (43375626123763/100000000000000 : ℝ)^3775
        have hw : |(40498551/78125000 : ℝ)|=(40498551/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681785811/1250000000 : ℝ)|^4799 ≤ (46272816442689/100000000000000 : ℝ)^3775
        have hw : |(681785811/1250000000 : ℝ)|=(681785811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s4_5 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279074993/10000000000 : ℝ)*x 0 + (-77422251/500000000 : ℝ)*x 1 + (5454286603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279074993/10000000000 : ℝ)^4799 ≤ (1775658063641/4000000000000 : ℝ)^3775 := by
    have hnat : (5279074993 : ℕ)^4799*4000000000000^3775 ≤ 1775658063641^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279074993 10000000000 1775658063641 4000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77422251/500000000 : ℝ)^4799 ≤ (93357307203/1000000000000 : ℝ)^3775 := by
    have hnat : (77422251 : ℕ)^4799*1000000000000^3775 ≤ 93357307203^3775*500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77422251 500000000 93357307203 1000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454286603/10000000000 : ℝ)^4799 ≤ (46272817682969/100000000000000 : ℝ)^3775 := by
    have hnat : (5454286603 : ℕ)^4799*100000000000000^3775 ≤ 46272817682969^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454286603 10000000000 46272817682969 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279074993/10000000000 : ℝ), (-77422251/500000000 : ℝ), (5454286603/10000000000 : ℝ)] ![(1775658063641/4000000000000 : ℝ), (93357307203/1000000000000 : ℝ), (46272817682969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279074993/10000000000 : ℝ)|^4799 ≤ (1775658063641/4000000000000 : ℝ)^3775
        have hw : |(5279074993/10000000000 : ℝ)|=(5279074993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77422251/500000000 : ℝ)|^4799 ≤ (93357307203/1000000000000 : ℝ)^3775
        have hw : |(-77422251/500000000 : ℝ)|=(77422251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454286603/10000000000 : ℝ)|^4799 ≤ (46272817682969/100000000000000 : ℝ)^3775
        have hw : |(5454286603/10000000000 : ℝ)|=(5454286603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s4_6 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527907501/1000000000 : ℝ)*x 0 + (5454286537/10000000000 : ℝ)*x 1 + (-48388909/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527907501/1000000000 : ℝ)^4799 ≤ (22195725886377/50000000000000 : ℝ)^3775 := by
    have hnat : (527907501 : ℕ)^4799*50000000000000^3775 ≤ 22195725886377^3775*1000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527907501 1000000000 22195725886377 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454286537/10000000000 : ℝ)^4799 ≤ (11568204242789/25000000000000 : ℝ)^3775 := by
    have hnat : (5454286537 : ℕ)^4799*25000000000000^3775 ≤ 11568204242789^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454286537 10000000000 11568204242789 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48388909/312500000 : ℝ)^4799 ≤ (9335731241489/100000000000000 : ℝ)^3775 := by
    have hnat : (48388909 : ℕ)^4799*100000000000000^3775 ≤ 9335731241489^3775*312500000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48388909 312500000 9335731241489 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527907501/1000000000 : ℝ), (5454286537/10000000000 : ℝ), (-48388909/312500000 : ℝ)] ![(22195725886377/50000000000000 : ℝ), (11568204242789/25000000000000 : ℝ), (9335731241489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527907501/1000000000 : ℝ)|^4799 ≤ (22195725886377/50000000000000 : ℝ)^3775
        have hw : |(527907501/1000000000 : ℝ)|=(527907501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454286537/10000000000 : ℝ)|^4799 ≤ (11568204242789/25000000000000 : ℝ)^3775
        have hw : |(5454286537/10000000000 : ℝ)|=(5454286537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48388909/312500000 : ℝ)|^4799 ≤ (9335731241489/100000000000000 : ℝ)^3775
        have hw : |(-48388909/312500000 : ℝ)|=(48388909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s4_7 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4204550751/10000000000 : ℝ)*x 0 + (4551646777/10000000000 : ℝ)*x 1 + (242390299/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204550751/10000000000 : ℝ)^4799 ≤ (8309797372279/25000000000000 : ℝ)^3775 := by
    have hnat : (4204550751 : ℕ)^4799*25000000000000^3775 ≤ 8309797372279^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204550751 10000000000 8309797372279 25000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4551646777/10000000000 : ℝ)^4799 ≤ (36765793363917/100000000000000 : ℝ)^3775 := by
    have hnat : (4551646777 : ℕ)^4799*100000000000000^3775 ≤ 36765793363917^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551646777 10000000000 36765793363917 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242390299/625000000 : ℝ)^4799 ≤ (29995017134091/100000000000000 : ℝ)^3775 := by
    have hnat : (242390299 : ℕ)^4799*100000000000000^3775 ≤ 29995017134091^3775*625000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242390299 625000000 29995017134091 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204550751/10000000000 : ℝ), (4551646777/10000000000 : ℝ), (242390299/625000000 : ℝ)] ![(8309797372279/25000000000000 : ℝ), (36765793363917/100000000000000 : ℝ), (29995017134091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204550751/10000000000 : ℝ)|^4799 ≤ (8309797372279/25000000000000 : ℝ)^3775
        have hw : |(4204550751/10000000000 : ℝ)|=(4204550751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4551646777/10000000000 : ℝ)|^4799 ≤ (36765793363917/100000000000000 : ℝ)^3775
        have hw : |(4551646777/10000000000 : ℝ)|=(4551646777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(242390299/625000000 : ℝ)|^4799 ≤ (29995017134091/100000000000000 : ℝ)^3775
        have hw : |(242390299/625000000 : ℝ)|=(242390299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1620_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8167/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1049/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10499/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4081/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8167/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1049/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8167/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1049/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8167/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1049/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8167/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1049/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8167/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1049/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8167/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1049/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1049/10000 : ℝ) ^ (4795/1024 : ℝ) ≤ (2598163459625209/100000000000000000000 : ℝ) := by
    have hpowers : (1049/10000 : ℝ)^4795 ≤ (2598163459625209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1049 : ℕ)^4795*100000000000000000000^1024 ≤ 2598163459625209^1024*10000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1049 10000 2598163459625209 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1049/10000 : ℝ)) (X := (2598163459625209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8167/50000 : ℝ) ^ (4795/1024 : ℝ) ≤ (20663964902559861/100000000000000000000 : ℝ) := by
    have hpowers : (8167/50000 : ℝ)^4795 ≤ (20663964902559861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8167 : ℕ)^4795*100000000000000000000^1024 ≤ 20663964902559861^1024*50000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8167 50000 20663964902559861 100000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8167/50000 : ℝ)) (X := (20663964902559861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002598163459625209/50000000000000000000 : ℝ) ≤ (10000110968301217/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50002598163459625209/50000000000000000000 : ℝ)^1024 ≤ (10000110968301217/10000000000000000 : ℝ)^4795 := by
      have hnat : (50002598163459625209 : ℕ)^1024*10000000000000000^4795 ≤ 10000110968301217^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002598163459625209 50000000000000000000 10000110968301217 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000110968301217/10000000000000000 : ℝ)) (X := (50002598163459625209/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002326212836218507/10000000000000000000 : ℝ) ≤ (7812888070921/7812500000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (10002326212836218507/10000000000000000000 : ℝ)^1024 ≤ (7812888070921/7812500000000 : ℝ)^4795 := by
      have hnat : (10002326212836218507 : ℕ)^1024*7812500000000^4795 ≤ 7812888070921^4795*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002326212836218507 10000000000000000000 7812888070921 7812500000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (7812888070921/7812500000000 : ℝ)) (X := (10002326212836218507/10000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020663964902559861/50000000000000000000 : ℝ) ≤ (10000882493256543/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (50020663964902559861/50000000000000000000 : ℝ)^1024 ≤ (10000882493256543/10000000000000000 : ℝ)^4795 := by
      have hnat : (50020663964902559861 : ℕ)^1024*10000000000000000^4795 ≤ 10000882493256543^4795*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020663964902559861 50000000000000000000 10000882493256543 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000882493256543/10000000000000000 : ℝ)) (X := (50020663964902559861/50000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2598163459625209/100000000000000000000 : ℝ) ≤ ((7304069400246367801/7305000000000000000 : ℝ)+2*(385762477663/584400000000000 : ℝ)*(1049/10000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (7304069400246367801/7305000000000000000 : ℝ)+2*(385762477663/584400000000000 : ℝ)*(1049/10000 : ℝ)=(10000110968301217/10000000000000000 : ℝ) by norm_num, show 1+2*(2598163459625209/100000000000000000000 : ℝ)=(50002598163459625209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20663964902559861/100000000000000000000 : ℝ)+(2598163459625209/100000000000000000000 : ℝ) ≤ ((7304069400246367801/7305000000000000000 : ℝ)+(385762477663/584400000000000 : ℝ)*((8167/50000 : ℝ)+(1049/10000 : ℝ)))^(4795/1024 : ℝ) := by
    rw [show (7304069400246367801/7305000000000000000 : ℝ)+(385762477663/584400000000000 : ℝ)*((8167/50000 : ℝ)+(1049/10000 : ℝ))=(7812888070921/7812500000000 : ℝ) by norm_num, show 1+(20663964902559861/100000000000000000000 : ℝ)+(2598163459625209/100000000000000000000 : ℝ)=(10002326212836218507/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20663964902559861/100000000000000000000 : ℝ) ≤ ((7304069400246367801/7305000000000000000 : ℝ)+2*(385762477663/584400000000000 : ℝ)*(8167/50000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (7304069400246367801/7305000000000000000 : ℝ)+2*(385762477663/584400000000000 : ℝ)*(8167/50000 : ℝ)=(10000882493256543/10000000000000000 : ℝ) by norm_num, show 1+2*(20663964902559861/100000000000000000000 : ℝ)=(50020663964902559861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7304069400246367801/7305000000000000000 : ℝ)*(X 1 0+X 2 0)+(385762477663/584400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (1049/10000 : ℝ)) (hi := (8167/50000 : ℝ)) (c := (7304069400246367801/7305000000000000000 : ℝ)) (alpha := (385762477663/584400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7304069400246367801/7305000000000000000 : ℝ)*(X 0 1+X 2 1)+(385762477663/584400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (1049/10000 : ℝ)) (hi := (8167/50000 : ℝ)) (c := (7304069400246367801/7305000000000000000 : ℝ)) (alpha := (385762477663/584400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7304069400246367801/7305000000000000000 : ℝ)*(X 0 2+X 1 2)+(385762477663/584400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (1049/10000 : ℝ)) (hi := (8167/50000 : ℝ)) (c := (7304069400246367801/7305000000000000000 : ℝ)) (alpha := (385762477663/584400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419859387/2500000000 : ℝ)*X 0 0+(682044649/1250000000 : ℝ)*X 0 1+(20241271/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352124963/10000000000 : ℝ)*X 1 0+(-455241587/2500000000 : ℝ)*X 1 1+(1036353073/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676062481/5000000000 : ℝ)*X 2 0+(518176537/1000000000 : ℝ)*X 2 1+(-910483171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840876029/2000000000 : ℝ)*X 0 0+(3873089257/10000000000 : ℝ)*X 0 1+(4556748499/10000000000 : ℝ)*X 0 2+(840876029/2000000000 : ℝ)*X 1 0+(3873089257/10000000000 : ℝ)*X 1 1+(4556748499/10000000000 : ℝ)*X 1 2+(840876029/2000000000 : ℝ)*X 2 0+(3873089257/10000000000 : ℝ)*X 2 1+(4556748499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1679506157/10000000000 : ℝ)*X 0 0+(40498551/78125000 : ℝ)*X 0 1+(681785811/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279074993/10000000000 : ℝ)*X 1 0+(-77422251/500000000 : ℝ)*X 1 1+(5454286603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527907501/1000000000 : ℝ)*X 2 0+(5454286537/10000000000 : ℝ)*X 2 1+(-48388909/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204550751/10000000000 : ℝ)*X 0 0+(4551646777/10000000000 : ℝ)*X 0 1+(242390299/625000000 : ℝ)*X 0 2+(4204550751/10000000000 : ℝ)*X 1 0+(4551646777/10000000000 : ℝ)*X 1 1+(242390299/625000000 : ℝ)*X 1 2+(4204550751/10000000000 : ℝ)*X 2 0+(4551646777/10000000000 : ℝ)*X 2 1+(242390299/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32574744974188428785410849/6087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (890722927/100000000000000 : ℝ)*(base19) + (832083151/100000000000000 : ℝ)*(base23) + (15510281/50000000000000 : ℝ)*(lower2) + (131926757/100000000000000 : ℝ)*(upper3) + (94071357/100000000000000 : ℝ)*(upper5) + (255225848102399/10000000000000 : ℝ)*(major0) + (255225848102399/10000000000000 : ℝ)*(major1) + (255225848102399/10000000000000 : ℝ)*(major2) + (1820890074448243/50000000000000 : ℝ)*(sp0) + (364179001838499/10000000000000 : ℝ)*(sp1) + (1820895038512383/50000000000000 : ℝ)*(sp2) + (468070781027/32000000000 : ℝ)*(sp3) + (10760211431/100000000000000 : ℝ)*(sp4) + (4683861099/100000000000000 : ℝ)*(sp7) + (731362937285237/50000000000000 : ℝ)*(f.failure) + (910447727276979/25000000000000 : ℝ)*(f.sum) + (12083434529399/2922000000000000000000000000 : ℝ)*base65 + (236046914906410967/24350000000000000000000000000000 : ℝ)*base68 + (11221500176139033/24350000000000000000000000000000 : ℝ)*base69 + (212792443711010967/24350000000000000000000000000000 : ℝ)*base72 + (10845026249779/2922000000000000000000000000 : ℝ)*base74 + (50348894087960967/24350000000000000000000000000000 : ℝ)*base76 + (185454784471710967/24350000000000000000000000000000 : ℝ)*base78 + (52741491655410967/24350000000000000000000000000000 : ℝ)*base80 + (14094495068519/2922000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4027281/1250000000000000000000 : ℝ)*base89 + (4027281/1250000000000000000000 : ℝ)*base91 + (4027281/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (583401146390779828129424829/121750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (420329197/50000000000000 : ℝ)*(base19) + (425829837/50000000000000 : ℝ)*(base23) + (62234381/20000000000000 : ℝ)*(lower1) + (55537/1562500000000 : ℝ)*(upper2) + (49221809/50000000000000 : ℝ)*(upper3) + (41252371/50000000000000 : ℝ)*(upper5) + (2591110867246371/100000000000000 : ℝ)*(major0) + (2591110867246371/100000000000000 : ℝ)*(major1) + (2591110867246371/100000000000000 : ℝ)*(major2) + (275975261/50000000000000 : ℝ)*(sp1) + (3697228993653733/100000000000000 : ℝ)*(sp4) + (1848613800522409/50000000000000 : ℝ)*(sp5) + (1848614070997029/50000000000000 : ℝ)*(sp6) + (148499258111247/10000000000000 : ℝ)*(sp7) + (148499258111247/10000000000000 : ℝ)*(f.failure) + (3697228993653733/100000000000000 : ℝ)*(f.sum) + (26642911578131/9740000000000000000000000000 : ℝ)*base65 + (1905577706802887557/243500000000000000000000000000000 : ℝ)*base67 + (4430359004892112443/243500000000000000000000000000000 : ℝ)*base70 + (1109907435956887557/243500000000000000000000000000000 : ℝ)*base71 + (46671874682231/9740000000000000000000000000 : ℝ)*base73 + (2984111228372112443/243500000000000000000000000000000 : ℝ)*base76 + (1927294659486887557/243500000000000000000000000000000 : ℝ)*base77 + (3377154343095887557/243500000000000000000000000000000 : ℝ)*base79 + (94183137285249/9740000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (81411/250000000000000000000 : ℝ)*base89 + (81411/250000000000000000000 : ℝ)*base91 + (81411/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1620_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8167/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1049/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4081/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1620_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1620_s5_0 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1679445017/10000000000 : ℝ)*x 0 + (5456319081/10000000000 : ℝ)*x 1 + (5181798523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1679445017/10000000000 : ℝ)^4799 ≤ (10351078365057/100000000000000 : ℝ)^3775 := by
    have hnat : (1679445017 : ℕ)^4799*100000000000000^3775 ≤ 10351078365057^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679445017 10000000000 10351078365057 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456319081/10000000000 : ℝ)^4799 ≤ (23147369574257/50000000000000 : ℝ)^3775 := by
    have hnat : (5456319081 : ℕ)^4799*50000000000000^3775 ≤ 23147369574257^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456319081 10000000000 23147369574257 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181798523/10000000000 : ℝ)^4799 ≤ (43354182469777/100000000000000 : ℝ)^3775 := by
    have hnat : (5181798523 : ℕ)^4799*100000000000000^3775 ≤ 43354182469777^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181798523 10000000000 43354182469777 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1679445017/10000000000 : ℝ), (5456319081/10000000000 : ℝ), (5181798523/10000000000 : ℝ)] ![(10351078365057/100000000000000 : ℝ), (23147369574257/50000000000000 : ℝ), (43354182469777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1679445017/10000000000 : ℝ)|^4799 ≤ (10351078365057/100000000000000 : ℝ)^3775
        have hw : |(-1679445017/10000000000 : ℝ)|=(1679445017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456319081/10000000000 : ℝ)|^4799 ≤ (23147369574257/50000000000000 : ℝ)^3775
        have hw : |(5456319081/10000000000 : ℝ)|=(5456319081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181798523/10000000000 : ℝ)|^4799 ≤ (43354182469777/100000000000000 : ℝ)^3775
        have hw : |(5181798523/10000000000 : ℝ)|=(5181798523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s5_1 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352114711/10000000000 : ℝ)*x 0 + (-364187301/2000000000 : ℝ)*x 1 + (5181798179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352114711/10000000000 : ℝ)^4799 ≤ (22586851072827/50000000000000 : ℝ)^3775 := by
    have hnat : (5352114711 : ℕ)^4799*50000000000000^3775 ≤ 22586851072827^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352114711 10000000000 22586851072827 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364187301/2000000000 : ℝ)^4799 ≤ (11472119025621/100000000000000 : ℝ)^3775 := by
    have hnat : (364187301 : ℕ)^4799*100000000000000^3775 ≤ 11472119025621^3775*2000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364187301 2000000000 11472119025621 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181798179/10000000000 : ℝ)^4799 ≤ (43354178810943/100000000000000 : ℝ)^3775 := by
    have hnat : (5181798179 : ℕ)^4799*100000000000000^3775 ≤ 43354178810943^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181798179 10000000000 43354178810943 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352114711/10000000000 : ℝ), (-364187301/2000000000 : ℝ), (5181798179/10000000000 : ℝ)] ![(22586851072827/50000000000000 : ℝ), (11472119025621/100000000000000 : ℝ), (43354178810943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352114711/10000000000 : ℝ)|^4799 ≤ (22586851072827/50000000000000 : ℝ)^3775
        have hw : |(5352114711/10000000000 : ℝ)|=(5352114711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-364187301/2000000000 : ℝ)|^4799 ≤ (11472119025621/100000000000000 : ℝ)^3775
        have hw : |(-364187301/2000000000 : ℝ)|=(364187301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181798179/10000000000 : ℝ)|^4799 ≤ (43354178810943/100000000000000 : ℝ)^3775
        have hw : |(5181798179/10000000000 : ℝ)|=(5181798179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s5_2 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352114797/10000000000 : ℝ)*x 0 + (5181798127/10000000000 : ℝ)*x 1 + (-1820936459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352114797/10000000000 : ℝ)^4799 ≤ (22586851534211/50000000000000 : ℝ)^3775 := by
    have hnat : (5352114797 : ℕ)^4799*50000000000000^3775 ≤ 22586851534211^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352114797 10000000000 22586851534211 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181798127/10000000000 : ℝ)^4799 ≤ (43354178257863/100000000000000 : ℝ)^3775 := by
    have hnat : (5181798127 : ℕ)^4799*100000000000000^3775 ≤ 43354178257863^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181798127 10000000000 43354178257863 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1820936459/10000000000 : ℝ)^4799 ≤ (11472118657203/100000000000000 : ℝ)^3775 := by
    have hnat : (1820936459 : ℕ)^4799*100000000000000^3775 ≤ 11472118657203^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820936459 10000000000 11472118657203 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352114797/10000000000 : ℝ), (5181798127/10000000000 : ℝ), (-1820936459/10000000000 : ℝ)] ![(22586851534211/50000000000000 : ℝ), (43354178257863/100000000000000 : ℝ), (11472118657203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352114797/10000000000 : ℝ)|^4799 ≤ (22586851534211/50000000000000 : ℝ)^3775
        have hw : |(5352114797/10000000000 : ℝ)|=(5352114797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181798127/10000000000 : ℝ)|^4799 ≤ (43354178257863/100000000000000 : ℝ)^3775
        have hw : |(5181798127/10000000000 : ℝ)|=(5181798127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1820936459/10000000000 : ℝ)|^4799 ≤ (11472118657203/100000000000000 : ℝ)^3775
        have hw : |(-1820936459/10000000000 : ℝ)|=(1820936459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s5_3 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4204385069/10000000000 : ℝ)*x 0 + (242073607/625000000 : ℝ)*x 1 + (4556659041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204385069/10000000000 : ℝ)^4799 ≤ (16618762199721/50000000000000 : ℝ)^3775 := by
    have hnat : (4204385069 : ℕ)^4799*50000000000000^3775 ≤ 16618762199721^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204385069 10000000000 16618762199721 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242073607/625000000 : ℝ)^4799 ≤ (29945205845547/100000000000000 : ℝ)^3775 := by
    have hnat : (242073607 : ℕ)^4799*100000000000000^3775 ≤ 29945205845547^3775*625000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242073607 625000000 29945205845547 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4556659041/10000000000 : ℝ)^4799 ≤ (4602158717471/12500000000000 : ℝ)^3775 := by
    have hnat : (4556659041 : ℕ)^4799*12500000000000^3775 ≤ 4602158717471^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556659041 10000000000 4602158717471 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204385069/10000000000 : ℝ), (242073607/625000000 : ℝ), (4556659041/10000000000 : ℝ)] ![(16618762199721/50000000000000 : ℝ), (29945205845547/100000000000000 : ℝ), (4602158717471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204385069/10000000000 : ℝ)|^4799 ≤ (16618762199721/50000000000000 : ℝ)^3775
        have hw : |(4204385069/10000000000 : ℝ)|=(4204385069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242073607/625000000 : ℝ)|^4799 ≤ (29945205845547/100000000000000 : ℝ)^3775
        have hw : |(242073607/625000000 : ℝ)|=(242073607/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4556659041/10000000000 : ℝ)|^4799 ≤ (4602158717471/12500000000000 : ℝ)^3775
        have hw : |(4556659041/10000000000 : ℝ)|=(4556659041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s5_4 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1679513569/10000000000 : ℝ)*x 0 + (1295961667/2500000000 : ℝ)*x 1 + (1363562351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1679513569/10000000000 : ℝ)^4799 ≤ (10351615491007/100000000000000 : ℝ)^3775 := by
    have hnat : (1679513569 : ℕ)^4799*100000000000000^3775 ≤ 10351615491007^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679513569 10000000000 10351615491007 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295961667/2500000000 : ℝ)^4799 ≤ (542199600073/1250000000000 : ℝ)^3775 := by
    have hnat : (1295961667 : ℕ)^4799*1250000000000^3775 ≤ 542199600073^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295961667 2500000000 542199600073 1250000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363562351/2500000000 : ℝ)^4799 ≤ (23136208245307/50000000000000 : ℝ)^3775 := by
    have hnat : (1363562351 : ℕ)^4799*50000000000000^3775 ≤ 23136208245307^3775*2500000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363562351 2500000000 23136208245307 50000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1679513569/10000000000 : ℝ), (1295961667/2500000000 : ℝ), (1363562351/2500000000 : ℝ)] ![(10351615491007/100000000000000 : ℝ), (542199600073/1250000000000 : ℝ), (23136208245307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1679513569/10000000000 : ℝ)|^4799 ≤ (10351615491007/100000000000000 : ℝ)^3775
        have hw : |(-1679513569/10000000000 : ℝ)|=(1679513569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295961667/2500000000 : ℝ)|^4799 ≤ (542199600073/1250000000000 : ℝ)^3775
        have hw : |(1295961667/2500000000 : ℝ)|=(1295961667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363562351/2500000000 : ℝ)|^4799 ≤ (23136208245307/50000000000000 : ℝ)^3775
        have hw : |(1363562351/2500000000 : ℝ)|=(1363562351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s5_5 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279083873/10000000000 : ℝ)*x 0 + (-1548485047/10000000000 : ℝ)*x 1 + (2727124677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279083873/10000000000 : ℝ)^4799 ≤ (44391546517723/100000000000000 : ℝ)^3775 := by
    have hnat : (5279083873 : ℕ)^4799*100000000000000^3775 ≤ 44391546517723^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279083873 10000000000 44391546517723 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1548485047/10000000000 : ℝ)^4799 ≤ (9336037510077/100000000000000 : ℝ)^3775 := by
    have hnat : (1548485047 : ℕ)^4799*100000000000000^3775 ≤ 9336037510077^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548485047 10000000000 9336037510077 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727124677/5000000000 : ℝ)^4799 ≤ (46272415951363/100000000000000 : ℝ)^3775 := by
    have hnat : (2727124677 : ℕ)^4799*100000000000000^3775 ≤ 46272415951363^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727124677 5000000000 46272415951363 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279083873/10000000000 : ℝ), (-1548485047/10000000000 : ℝ), (2727124677/5000000000 : ℝ)] ![(44391546517723/100000000000000 : ℝ), (9336037510077/100000000000000 : ℝ), (46272415951363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279083873/10000000000 : ℝ)|^4799 ≤ (44391546517723/100000000000000 : ℝ)^3775
        have hw : |(5279083873/10000000000 : ℝ)|=(5279083873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1548485047/10000000000 : ℝ)|^4799 ≤ (9336037510077/100000000000000 : ℝ)^3775
        have hw : |(-1548485047/10000000000 : ℝ)|=(1548485047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727124677/5000000000 : ℝ)|^4799 ≤ (46272415951363/100000000000000 : ℝ)^3775
        have hw : |(2727124677/5000000000 : ℝ)|=(2727124677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s5_6 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279083347/10000000000 : ℝ)*x 0 + (5454249997/10000000000 : ℝ)*x 1 + (-774242439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279083347/10000000000 : ℝ)^4799 ≤ (44391540894811/100000000000000 : ℝ)^3775 := by
    have hnat : (5279083347 : ℕ)^4799*100000000000000^3775 ≤ 44391540894811^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279083347 10000000000 44391540894811 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454249997/10000000000 : ℝ)^4799 ≤ (46272422886131/100000000000000 : ℝ)^3775 := by
    have hnat : (5454249997 : ℕ)^4799*100000000000000^3775 ≤ 46272422886131^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454249997 10000000000 46272422886131 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774242439/5000000000 : ℝ)^4799 ≤ (233400905369/2500000000000 : ℝ)^3775 := by
    have hnat : (774242439 : ℕ)^4799*2500000000000^3775 ≤ 233400905369^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774242439 5000000000 233400905369 2500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279083347/10000000000 : ℝ), (5454249997/10000000000 : ℝ), (-774242439/5000000000 : ℝ)] ![(44391540894811/100000000000000 : ℝ), (46272422886131/100000000000000 : ℝ), (233400905369/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279083347/10000000000 : ℝ)|^4799 ≤ (44391540894811/100000000000000 : ℝ)^3775
        have hw : |(5279083347/10000000000 : ℝ)|=(5279083347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454249997/10000000000 : ℝ)|^4799 ≤ (46272422886131/100000000000000 : ℝ)^3775
        have hw : |(5454249997/10000000000 : ℝ)|=(5454249997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-774242439/5000000000 : ℝ)|^4799 ≤ (233400905369/2500000000000 : ℝ)^3775
        have hw : |(-774242439/5000000000 : ℝ)|=(774242439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1620_s5_7 (p : ℝ) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525569477/1250000000 : ℝ)*x 0 + (2275780179/5000000000 : ℝ)*x 1 + (3878329861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525569477/1250000000 : ℝ)^4799 ≤ (6647848078441/20000000000000 : ℝ)^3775 := by
    have hnat : (525569477 : ℕ)^4799*20000000000000^3775 ≤ 6647848078441^3775*1250000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525569477 1250000000 6647848078441 20000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275780179/5000000000 : ℝ)^4799 ≤ (36764905968253/100000000000000 : ℝ)^3775 := by
    have hnat : (2275780179 : ℕ)^4799*100000000000000^3775 ≤ 36764905968253^3775*5000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275780179 5000000000 36764905968253 100000000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3878329861/10000000000 : ℝ)^4799 ≤ (3749481703107/12500000000000 : ℝ)^3775 := by
    have hnat : (3878329861 : ℕ)^4799*12500000000000^3775 ≤ 3749481703107^3775*10000000000^4799 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3878329861 10000000000 3749481703107 12500000000000 4799 3775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4799/1024 : ℝ)) 4799 3775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525569477/1250000000 : ℝ), (2275780179/5000000000 : ℝ), (3878329861/10000000000 : ℝ)] ![(6647848078441/20000000000000 : ℝ), (36764905968253/100000000000000 : ℝ), (3749481703107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525569477/1250000000 : ℝ)|^4799 ≤ (6647848078441/20000000000000 : ℝ)^3775
        have hw : |(525569477/1250000000 : ℝ)|=(525569477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2275780179/5000000000 : ℝ)|^4799 ≤ (36764905968253/100000000000000 : ℝ)^3775
        have hw : |(2275780179/5000000000 : ℝ)|=(2275780179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3878329861/10000000000 : ℝ)|^4799 ≤ (3749481703107/12500000000000 : ℝ)^3775
        have hw : |(3878329861/10000000000 : ℝ)|=(3878329861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1620_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4081/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (21/200 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16323/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4081/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4081/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4081/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4081/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4081/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4081/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10499/100000 : ℝ) ^ (4795/1024 : ℝ) ≤ (1304309039381173/50000000000000000000 : ℝ) := by
    have hpowers : (10499/100000 : ℝ)^4795 ≤ (1304309039381173/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10499 : ℕ)^4795*50000000000000000000^1024 ≤ 1304309039381173^1024*100000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10499 100000 1304309039381173 50000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10499/100000 : ℝ)) (X := (1304309039381173/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4081/25000 : ℝ) ^ (4795/1024 : ℝ) ≤ (10302396183641361/50000000000000000000 : ℝ) := by
    have hpowers : (4081/25000 : ℝ)^4795 ≤ (10302396183641361/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4081 : ℕ)^4795*50000000000000000000^1024 ≤ 10302396183641361^1024*25000^4795 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4081 25000 10302396183641361 50000000000000000000 4795 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4081/25000 : ℝ)) (X := (10302396183641361/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001304309039381173/25000000000000000000 : ℝ) ≤ (10000111414811817/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (25001304309039381173/25000000000000000000 : ℝ)^1024 ≤ (10000111414811817/10000000000000000 : ℝ)^4795 := by
      have hnat : (25001304309039381173 : ℕ)^1024*10000000000000000^4795 ≤ 10000111414811817^4795*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001304309039381173 25000000000000000000 10000111414811817 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000111414811817/10000000000000000 : ℝ)) (X := (25001304309039381173/25000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005803352611511267/25000000000000000000 : ℝ) ≤ (5000247845284841/5000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (25005803352611511267/25000000000000000000 : ℝ)^1024 ≤ (5000247845284841/5000000000000000 : ℝ)^4795 := by
      have hnat : (25005803352611511267 : ℕ)^1024*5000000000000000^4795 ≤ 5000247845284841^4795*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005803352611511267 25000000000000000000 5000247845284841 5000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000247845284841/5000000000000000 : ℝ)) (X := (25005803352611511267/25000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010302396183641361/25000000000000000000 : ℝ) ≤ (10000879966327547/10000000000000000 : ℝ) ^ (4795/1024 : ℝ) := by
    have hpowers : (25010302396183641361/25000000000000000000 : ℝ)^1024 ≤ (10000879966327547/10000000000000000 : ℝ)^4795 := by
      have hnat : (25010302396183641361 : ℕ)^1024*10000000000000000^4795 ≤ 10000879966327547^4795*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010302396183641361 25000000000000000000 10000879966327547 10000000000000000 1024 4795 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000879966327547/10000000000000000 : ℝ)) (X := (25010302396183641361/25000000000000000000 : ℝ)) (by norm_num) 4795 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1304309039381173/50000000000000000000 : ℝ) ≤ ((11648515993783036951/11650000000000000000 : ℝ)+2*(76855151573/116500000000000 : ℝ)*(10499/100000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (11648515993783036951/11650000000000000000 : ℝ)+2*(76855151573/116500000000000 : ℝ)*(10499/100000 : ℝ)=(10000111414811817/10000000000000000 : ℝ) by norm_num, show 1+2*(1304309039381173/50000000000000000000 : ℝ)=(25001304309039381173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10302396183641361/50000000000000000000 : ℝ)+(1304309039381173/50000000000000000000 : ℝ) ≤ ((11648515993783036951/11650000000000000000 : ℝ)+(76855151573/116500000000000 : ℝ)*((4081/25000 : ℝ)+(10499/100000 : ℝ)))^(4795/1024 : ℝ) := by
    rw [show (11648515993783036951/11650000000000000000 : ℝ)+(76855151573/116500000000000 : ℝ)*((4081/25000 : ℝ)+(10499/100000 : ℝ))=(5000247845284841/5000000000000000 : ℝ) by norm_num, show 1+(10302396183641361/50000000000000000000 : ℝ)+(1304309039381173/50000000000000000000 : ℝ)=(25005803352611511267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10302396183641361/50000000000000000000 : ℝ) ≤ ((11648515993783036951/11650000000000000000 : ℝ)+2*(76855151573/116500000000000 : ℝ)*(4081/25000 : ℝ))^(4795/1024 : ℝ) := by
    rw [show (11648515993783036951/11650000000000000000 : ℝ)+2*(76855151573/116500000000000 : ℝ)*(4081/25000 : ℝ)=(10000879966327547/10000000000000000 : ℝ) by norm_num, show 1+2*(10302396183641361/50000000000000000000 : ℝ)=(25010302396183641361/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11648515993783036951/11650000000000000000 : ℝ)*(X 1 0+X 2 0)+(76855151573/116500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (10499/100000 : ℝ)) (hi := (4081/25000 : ℝ)) (c := (11648515993783036951/11650000000000000000 : ℝ)) (alpha := (76855151573/116500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11648515993783036951/11650000000000000000 : ℝ)*(X 0 1+X 2 1)+(76855151573/116500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (10499/100000 : ℝ)) (hi := (4081/25000 : ℝ)) (c := (11648515993783036951/11650000000000000000 : ℝ)) (alpha := (76855151573/116500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11648515993783036951/11650000000000000000 : ℝ)*(X 0 2+X 1 2)+(76855151573/116500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4795/1024 : ℝ)) (lo := (10499/100000 : ℝ)) (hi := (4081/25000 : ℝ)) (c := (11648515993783036951/11650000000000000000 : ℝ)) (alpha := (76855151573/116500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1679445017/10000000000 : ℝ)*X 0 0+(5456319081/10000000000 : ℝ)*X 0 1+(5181798523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352114711/10000000000 : ℝ)*X 1 0+(-364187301/2000000000 : ℝ)*X 1 1+(5181798179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352114797/10000000000 : ℝ)*X 2 0+(5181798127/10000000000 : ℝ)*X 2 1+(-1820936459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4204385069/10000000000 : ℝ)*X 0 0+(242073607/625000000 : ℝ)*X 0 1+(4556659041/10000000000 : ℝ)*X 0 2+(4204385069/10000000000 : ℝ)*X 1 0+(242073607/625000000 : ℝ)*X 1 1+(4556659041/10000000000 : ℝ)*X 1 2+(4204385069/10000000000 : ℝ)*X 2 0+(242073607/625000000 : ℝ)*X 2 1+(4556659041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1679513569/10000000000 : ℝ)*X 0 0+(1295961667/2500000000 : ℝ)*X 0 1+(1363562351/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279083873/10000000000 : ℝ)*X 1 0+(-1548485047/10000000000 : ℝ)*X 1 1+(2727124677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279083347/10000000000 : ℝ)*X 2 0+(5454249997/10000000000 : ℝ)*X 2 1+(-774242439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525569477/1250000000 : ℝ)*X 0 0+(2275780179/5000000000 : ℝ)*X 0 1+(3878329861/10000000000 : ℝ)*X 0 2+(525569477/1250000000 : ℝ)*X 1 0+(2275780179/5000000000 : ℝ)*X 1 1+(3878329861/10000000000 : ℝ)*X 1 2+(525569477/1250000000 : ℝ)*X 2 0+(2275780179/5000000000 : ℝ)*X 2 1+(3878329861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1620_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12092281750915960471058943/4550781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (144548159/50000000000000 : ℝ)*(base19) + (25548049/10000000000000 : ℝ)*(base23) + (53821367/100000000000000 : ℝ)*(lower2) + (8193767/12500000000000 : ℝ)*(upper3) + (1435519/50000000000000 : ℝ)*(upper5) + (79778310129833/3125000000000 : ℝ)*(major0) + (79778310129833/3125000000000 : ℝ)*(major1) + (79778310129833/3125000000000 : ℝ)*(major2) + (455339353596927/12500000000000 : ℝ)*(sp0) + (728542529393971/20000000000000 : ℝ)*(sp1) + (9106783242773/250000000000 : ℝ)*(sp2) + (1463096930960953/100000000000000 : ℝ)*(sp3) + (1892709243/100000000000000 : ℝ)*(sp5) + (1276185727/100000000000000 : ℝ)*(sp6) + (1463096930960953/100000000000000 : ℝ)*(f.failure) + (455339353596927/12500000000000 : ℝ)*(f.sum) + (12582344416237/5825000000000000000000000000 : ℝ)*base66 + (166604836743890817/36406250000000000000000000000000 : ℝ)*base68 + (97740391009047067/36406250000000000000000000000000 : ℝ)*base70 + (124384274490297067/36406250000000000000000000000000 : ℝ)*base72 + (5312714867097/1456250000000000000000000000 : ℝ)*base73 + (167711838238265817/36406250000000000000000000000000 : ℝ)*base76 + (277699935525453317/36406250000000000000000000000000 : ℝ)*base78 + (696357587659359567/36406250000000000000000000000000 : ℝ)*base80 + (22715651091113/5825000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9877189/2500000000000000000000 : ℝ)*base89 + (9877189/2500000000000000000000 : ℝ)*base91 + (9877189/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (843372547834287545497900743/291250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13612361/3125000000000 : ℝ)*(base19) + (65484563/25000000000000 : ℝ)*(base23) + (77769911/100000000000000 : ℝ)*(lower1) + (20350013/20000000000000 : ℝ)*(upper3) + (66308141/100000000000000 : ℝ)*(lower4) + (1295888642093131/50000000000000 : ℝ)*(major0) + (1295888642093131/50000000000000 : ℝ)*(major1) + (1295888642093131/50000000000000 : ℝ)*(major2) + (500345573/10000000000000 : ℝ)*(sp2) + (34638957/25000000000000 : ℝ)*(sp3) + (924544990064719/25000000000000 : ℝ)*(sp4) + (924544881165831/25000000000000 : ℝ)*(sp5) + (1849087347432447/50000000000000 : ℝ)*(sp6) + (1485374373034483/100000000000000 : ℝ)*(sp7) + (1485374511590311/100000000000000 : ℝ)*(f.failure) + (924544990064719/25000000000000 : ℝ)*(f.sum) + (13790090793463/2912500000000000000000000000 : ℝ)*base65 + (2211215214422416419/582500000000000000000000000000000 : ℝ)*base68 + (903206860924916419/582500000000000000000000000000000 : ℝ)*base70 + (9413706125322583581/582500000000000000000000000000000 : ℝ)*base71 + (19015124127/11376953125000000000000000 : ℝ)*base74 + (3166675337264916419/582500000000000000000000000000000 : ℝ)*base76 + (28336344925302583581/582500000000000000000000000000000 : ℝ)*base77 + (18221983717872416419/582500000000000000000000000000000 : ℝ)*base80 + (42563641222299/5825000000000000000000000000 : ℝ)*base82 + (10991643/2500000000000000000000 : ℝ)*base89 + (10991643/2500000000000000000000 : ℝ)*base91 + (10991643/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1620_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4081/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1620_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1620_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1620_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1620_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1620_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4795/1024 : ℝ) ≤ p) (hpb : p ≤ (4799/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43621613/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/200 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1620_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
