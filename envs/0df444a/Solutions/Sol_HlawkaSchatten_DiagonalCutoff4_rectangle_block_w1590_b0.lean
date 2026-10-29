-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1590_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:56.995597+00:00
-- url     : https://prove2.me/submissions/0696f19d-53b2-4f9a-bcca-61de62b3b325

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
theorem support_rectangle_w1590_s0_0 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6416201/40000000 : ℝ)*x 0 + (733101177/1250000000 : ℝ)*x 1 + (4877673553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6416201/40000000 : ℝ)^4679 ≤ (4803065781307/50000000000000 : ℝ)^3655 := by
    have hnat : (6416201 : ℕ)^4679*50000000000000^3655 ≤ 4803065781307^3655*40000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6416201 40000000 4803065781307 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733101177/1250000000 : ℝ)^4679 ≤ (12626034228809/25000000000000 : ℝ)^3655 := by
    have hnat : (733101177 : ℕ)^4679*25000000000000^3655 ≤ 12626034228809^3655*1250000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733101177 1250000000 12626034228809 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4877673553/10000000000 : ℝ)^4679 ≤ (39889731505023/100000000000000 : ℝ)^3655 := by
    have hnat : (4877673553 : ℕ)^4679*100000000000000^3655 ≤ 39889731505023^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877673553 10000000000 39889731505023 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6416201/40000000 : ℝ), (733101177/1250000000 : ℝ), (4877673553/10000000000 : ℝ)] ![(4803065781307/50000000000000 : ℝ), (12626034228809/25000000000000 : ℝ), (39889731505023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6416201/40000000 : ℝ)|^4679 ≤ (4803065781307/50000000000000 : ℝ)^3655
        have hw : |(-6416201/40000000 : ℝ)|=(6416201/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733101177/1250000000 : ℝ)|^4679 ≤ (12626034228809/25000000000000 : ℝ)^3655
        have hw : |(733101177/1250000000 : ℝ)|=(733101177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4877673553/10000000000 : ℝ)|^4679 ≤ (39889731505023/100000000000000 : ℝ)^3655
        have hw : |(4877673553/10000000000 : ℝ)|=(4877673553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s0_1 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (682754183/1250000000 : ℝ)*x 0 + (-107655953/500000000 : ℝ)*x 1 + (4877673433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (682754183/1250000000 : ℝ)^4679 ≤ (46107381724077/100000000000000 : ℝ)^3655 := by
    have hnat : (682754183 : ℕ)^4679*100000000000000^3655 ≤ 46107381724077^3655*1250000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682754183 1250000000 46107381724077 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107655953/500000000 : ℝ)^4679 ≤ (14002888010707/100000000000000 : ℝ)^3655 := by
    have hnat : (107655953 : ℕ)^4679*100000000000000^3655 ≤ 14002888010707^3655*500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107655953 500000000 14002888010707 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4877673433/10000000000 : ℝ)^4679 ≤ (39889730248717/100000000000000 : ℝ)^3655 := by
    have hnat : (4877673433 : ℕ)^4679*100000000000000^3655 ≤ 39889730248717^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877673433 10000000000 39889730248717 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(682754183/1250000000 : ℝ), (-107655953/500000000 : ℝ), (4877673433/10000000000 : ℝ)] ![(46107381724077/100000000000000 : ℝ), (14002888010707/100000000000000 : ℝ), (39889730248717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(682754183/1250000000 : ℝ)|^4679 ≤ (46107381724077/100000000000000 : ℝ)^3655
        have hw : |(682754183/1250000000 : ℝ)|=(682754183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107655953/500000000 : ℝ)|^4679 ≤ (14002888010707/100000000000000 : ℝ)^3655
        have hw : |(-107655953/500000000 : ℝ)|=(107655953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4877673433/10000000000 : ℝ)|^4679 ≤ (39889730248717/100000000000000 : ℝ)^3655
        have hw : |(4877673433/10000000000 : ℝ)|=(4877673433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s0_2 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42672137/78125000 : ℝ)*x 0 + (4877673339/10000000000 : ℝ)*x 1 + (-430623817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42672137/78125000 : ℝ)^4679 ≤ (46107382502139/100000000000000 : ℝ)^3655 := by
    have hnat : (42672137 : ℕ)^4679*100000000000000^3655 ≤ 46107382502139^3655*78125000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42672137 78125000 46107382502139 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4877673339/10000000000 : ℝ)^4679 ≤ (39889729264611/100000000000000 : ℝ)^3655 := by
    have hnat : (4877673339 : ℕ)^4679*100000000000000^3655 ≤ 39889729264611^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877673339 10000000000 39889729264611 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430623817/2000000000 : ℝ)^4679 ≤ (14002888218847/100000000000000 : ℝ)^3655 := by
    have hnat : (430623817 : ℕ)^4679*100000000000000^3655 ≤ 14002888218847^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430623817 2000000000 14002888218847 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42672137/78125000 : ℝ), (4877673339/10000000000 : ℝ), (-430623817/2000000000 : ℝ)] ![(46107382502139/100000000000000 : ℝ), (39889729264611/100000000000000 : ℝ), (14002888218847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42672137/78125000 : ℝ)|^4679 ≤ (46107382502139/100000000000000 : ℝ)^3655
        have hw : |(42672137/78125000 : ℝ)|=(42672137/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4877673339/10000000000 : ℝ)|^4679 ≤ (39889729264611/100000000000000 : ℝ)^3655
        have hw : |(4877673339/10000000000 : ℝ)|=(4877673339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430623817/2000000000 : ℝ)|^4679 ≤ (14002888218847/100000000000000 : ℝ)^3655
        have hw : |(-430623817/2000000000 : ℝ)|=(430623817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s0_3 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4119724003/10000000000 : ℝ)*x 0 + (1535768503/5000000000 : ℝ)*x 1 + (5433510701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119724003/10000000000 : ℝ)^4679 ≤ (6426847116187/20000000000000 : ℝ)^3655 := by
    have hnat : (4119724003 : ℕ)^4679*20000000000000^3655 ≤ 6426847116187^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119724003 10000000000 6426847116187 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1535768503/5000000000 : ℝ)^4679 ≤ (22066385836517/100000000000000 : ℝ)^3655 := by
    have hnat : (1535768503 : ℕ)^4679*100000000000000^3655 ≤ 22066385836517^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535768503 5000000000 22066385836517 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433510701/10000000000 : ℝ)^4679 ≤ (45799378575891/100000000000000 : ℝ)^3655 := by
    have hnat : (5433510701 : ℕ)^4679*100000000000000^3655 ≤ 45799378575891^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433510701 10000000000 45799378575891 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119724003/10000000000 : ℝ), (1535768503/5000000000 : ℝ), (5433510701/10000000000 : ℝ)] ![(6426847116187/20000000000000 : ℝ), (22066385836517/100000000000000 : ℝ), (45799378575891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119724003/10000000000 : ℝ)|^4679 ≤ (6426847116187/20000000000000 : ℝ)^3655
        have hw : |(4119724003/10000000000 : ℝ)|=(4119724003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1535768503/5000000000 : ℝ)|^4679 ≤ (22066385836517/100000000000000 : ℝ)^3655
        have hw : |(1535768503/5000000000 : ℝ)|=(1535768503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433510701/10000000000 : ℝ)|^4679 ≤ (45799378575891/100000000000000 : ℝ)^3655
        have hw : |(5433510701/10000000000 : ℝ)|=(5433510701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s0_4 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-321425961/2000000000 : ℝ)*x 0 + (2451442709/5000000000 : ℝ)*x 1 + (5838690483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321425961/2000000000 : ℝ)^4679 ≤ (2407436816953/25000000000000 : ℝ)^3655 := by
    have hnat : (321425961 : ℕ)^4679*25000000000000^3655 ≤ 2407436816953^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321425961 2000000000 2407436816953 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2451442709/5000000000 : ℝ)^4679 ≤ (10038467693533/25000000000000 : ℝ)^3655 := by
    have hnat : (2451442709 : ℕ)^4679*25000000000000^3655 ≤ 10038467693533^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451442709 5000000000 10038467693533 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5838690483/10000000000 : ℝ)^4679 ≤ (50216381945271/100000000000000 : ℝ)^3655 := by
    have hnat : (5838690483 : ℕ)^4679*100000000000000^3655 ≤ 50216381945271^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5838690483 10000000000 50216381945271 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-321425961/2000000000 : ℝ), (2451442709/5000000000 : ℝ), (5838690483/10000000000 : ℝ)] ![(2407436816953/25000000000000 : ℝ), (10038467693533/25000000000000 : ℝ), (50216381945271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-321425961/2000000000 : ℝ)|^4679 ≤ (2407436816953/25000000000000 : ℝ)^3655
        have hw : |(-321425961/2000000000 : ℝ)|=(321425961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2451442709/5000000000 : ℝ)|^4679 ≤ (10038467693533/25000000000000 : ℝ)^3655
        have hw : |(2451442709/5000000000 : ℝ)|=(2451442709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5838690483/10000000000 : ℝ)|^4679 ≤ (50216381945271/100000000000000 : ℝ)^3655
        have hw : |(5838690483/10000000000 : ℝ)|=(5838690483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s0_5 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038482831/2000000000 : ℝ)*x 0 + (-1192102467/10000000000 : ℝ)*x 1 + (2919345381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038482831/2000000000 : ℝ)^4679 ≤ (43214153637267/100000000000000 : ℝ)^3655 := by
    have hnat : (1038482831 : ℕ)^4679*100000000000000^3655 ≤ 43214153637267^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038482831 2000000000 43214153637267 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192102467/10000000000 : ℝ)^4679 ≤ (6569461319199/100000000000000 : ℝ)^3655 := by
    have hnat : (1192102467 : ℕ)^4679*100000000000000^3655 ≤ 6569461319199^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192102467 10000000000 6569461319199 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2919345381/5000000000 : ℝ)^4679 ≤ (313852406357/625000000000 : ℝ)^3655 := by
    have hnat : (2919345381 : ℕ)^4679*625000000000^3655 ≤ 313852406357^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919345381 5000000000 313852406357 625000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038482831/2000000000 : ℝ), (-1192102467/10000000000 : ℝ), (2919345381/5000000000 : ℝ)] ![(43214153637267/100000000000000 : ℝ), (6569461319199/100000000000000 : ℝ), (313852406357/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038482831/2000000000 : ℝ)|^4679 ≤ (43214153637267/100000000000000 : ℝ)^3655
        have hw : |(1038482831/2000000000 : ℝ)|=(1038482831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1192102467/10000000000 : ℝ)|^4679 ≤ (6569461319199/100000000000000 : ℝ)^3655
        have hw : |(-1192102467/10000000000 : ℝ)|=(1192102467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2919345381/5000000000 : ℝ)|^4679 ≤ (313852406357/625000000000 : ℝ)^3655
        have hw : |(2919345381/5000000000 : ℝ)|=(2919345381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s0_6 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192413653/10000000000 : ℝ)*x 0 + (5838691527/10000000000 : ℝ)*x 1 + (-1192102033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192413653/10000000000 : ℝ)^4679 ≤ (1080353707221/2500000000000 : ℝ)^3655 := by
    have hnat : (5192413653 : ℕ)^4679*2500000000000^3655 ≤ 1080353707221^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192413653 10000000000 1080353707221 2500000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5838691527/10000000000 : ℝ)^4679 ≤ (50216393439931/100000000000000 : ℝ)^3655 := by
    have hnat : (5838691527 : ℕ)^4679*100000000000000^3655 ≤ 50216393439931^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5838691527 10000000000 50216393439931 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192102033/10000000000 : ℝ)^4679 ≤ (1642364564359/25000000000000 : ℝ)^3655 := by
    have hnat : (1192102033 : ℕ)^4679*25000000000000^3655 ≤ 1642364564359^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192102033 10000000000 1642364564359 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192413653/10000000000 : ℝ), (5838691527/10000000000 : ℝ), (-1192102033/10000000000 : ℝ)] ![(1080353707221/2500000000000 : ℝ), (50216393439931/100000000000000 : ℝ), (1642364564359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192413653/10000000000 : ℝ)|^4679 ≤ (1080353707221/2500000000000 : ℝ)^3655
        have hw : |(5192413653/10000000000 : ℝ)|=(5192413653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5838691527/10000000000 : ℝ)|^4679 ≤ (50216393439931/100000000000000 : ℝ)^3655
        have hw : |(5838691527/10000000000 : ℝ)|=(5838691527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1192102033/10000000000 : ℝ)|^4679 ≤ (1642364564359/25000000000000 : ℝ)^3655
        have hw : |(-1192102033/10000000000 : ℝ)|=(1192102033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s0_7 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4127090519/10000000000 : ℝ)*x 0 + (5373182187/10000000000 : ℝ)*x 1 + (1567015909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4127090519/10000000000 : ℝ)^4679 ≤ (16103905807493/50000000000000 : ℝ)^3655 := by
    have hnat : (4127090519 : ℕ)^4679*50000000000000^3655 ≤ 16103905807493^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127090519 10000000000 16103905807493 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5373182187/10000000000 : ℝ)^4679 ≤ (4514941422211/10000000000000 : ℝ)^3655 := by
    have hnat : (5373182187 : ℕ)^4679*10000000000000^3655 ≤ 4514941422211^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373182187 10000000000 4514941422211 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1567015909/5000000000 : ℝ)^4679 ≤ (1132138707331/5000000000000 : ℝ)^3655 := by
    have hnat : (1567015909 : ℕ)^4679*5000000000000^3655 ≤ 1132138707331^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567015909 5000000000 1132138707331 5000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4127090519/10000000000 : ℝ), (5373182187/10000000000 : ℝ), (1567015909/5000000000 : ℝ)] ![(16103905807493/50000000000000 : ℝ), (4514941422211/10000000000000 : ℝ), (1132138707331/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4127090519/10000000000 : ℝ)|^4679 ≤ (16103905807493/50000000000000 : ℝ)^3655
        have hw : |(4127090519/10000000000 : ℝ)|=(4127090519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5373182187/10000000000 : ℝ)|^4679 ≤ (4514941422211/10000000000000 : ℝ)^3655
        have hw : |(5373182187/10000000000 : ℝ)|=(5373182187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1567015909/5000000000 : ℝ)|^4679 ≤ (1132138707331/5000000000000 : ℝ)^3655
        have hw : |(1567015909/5000000000 : ℝ)|=(1567015909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1590_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1787/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3089/12500 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4675/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4675 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4675*1^1024 ≤ 0^1024*1^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4675/1024 : ℝ) ≤ (381217544139127491/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4675 ≤ (381217544139127491/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4675*25000000000000000000^1024 ≤ 381217544139127491^1024*5^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 381217544139127491 25000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (381217544139127491/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4675 := by
      have hnat : (1 : ℕ)^1024*1^4675 ≤ 1^4675*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25381217544139127491/25000000000000000000 : ℝ) ≤ (5016601634754607/5000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (25381217544139127491/25000000000000000000 : ℝ)^1024 ≤ (5016601634754607/5000000000000000 : ℝ)^4675 := by
      have hnat : (25381217544139127491 : ℕ)^1024*5000000000000000^4675 ≤ 5016601634754607^4675*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25381217544139127491 25000000000000000000 5016601634754607 5000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016601634754607/5000000000000000 : ℝ)) (X := (25381217544139127491/25000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12881217544139127491/12500000000000000000 : ℝ) ≤ (2516601634754607/2500000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (12881217544139127491/12500000000000000000 : ℝ)^1024 ≤ (2516601634754607/2500000000000000 : ℝ)^4675 := by
      have hnat : (12881217544139127491 : ℕ)^1024*2500000000000000^4675 ≤ 2516601634754607^4675*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12881217544139127491 12500000000000000000 2516601634754607 2500000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2516601634754607/2500000000000000 : ℝ)) (X := (12881217544139127491/12500000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(16601634754607/2000000000000000 : ℝ)*(0 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16601634754607/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(381217544139127491/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(16601634754607/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4675/1024 : ℝ) := by
    rw [show (1 : ℝ)+(16601634754607/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5016601634754607/5000000000000000 : ℝ) by norm_num, show 1+(381217544139127491/25000000000000000000 : ℝ)+(0 : ℝ)=(25381217544139127491/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(381217544139127491/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(16601634754607/2000000000000000 : ℝ)*(2/5 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16601634754607/2000000000000000 : ℝ)*(2/5 : ℝ)=(2516601634754607/2500000000000000 : ℝ) by norm_num, show 1+2*(381217544139127491/25000000000000000000 : ℝ)=(12881217544139127491/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(16601634754607/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16601634754607/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(16601634754607/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16601634754607/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(16601634754607/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16601634754607/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-6416201/40000000 : ℝ)*X 0 0+(733101177/1250000000 : ℝ)*X 0 1+(4877673553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((682754183/1250000000 : ℝ)*X 1 0+(-107655953/500000000 : ℝ)*X 1 1+(4877673433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42672137/78125000 : ℝ)*X 2 0+(4877673339/10000000000 : ℝ)*X 2 1+(-430623817/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4119724003/10000000000 : ℝ)*X 0 0+(1535768503/5000000000 : ℝ)*X 0 1+(5433510701/10000000000 : ℝ)*X 0 2+(4119724003/10000000000 : ℝ)*X 1 0+(1535768503/5000000000 : ℝ)*X 1 1+(5433510701/10000000000 : ℝ)*X 1 2+(4119724003/10000000000 : ℝ)*X 2 0+(1535768503/5000000000 : ℝ)*X 2 1+(5433510701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-321425961/2000000000 : ℝ)*X 0 0+(2451442709/5000000000 : ℝ)*X 0 1+(5838690483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1038482831/2000000000 : ℝ)*X 1 0+(-1192102467/10000000000 : ℝ)*X 1 1+(2919345381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192413653/10000000000 : ℝ)*X 2 0+(5838691527/10000000000 : ℝ)*X 2 1+(-1192102033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4127090519/10000000000 : ℝ)*X 0 0+(5373182187/10000000000 : ℝ)*X 0 1+(1567015909/5000000000 : ℝ)*X 0 2+(4127090519/10000000000 : ℝ)*X 1 0+(5373182187/10000000000 : ℝ)*X 1 1+(1567015909/5000000000 : ℝ)*X 1 2+(4127090519/10000000000 : ℝ)*X 2 0+(5373182187/10000000000 : ℝ)*X 2 1+(1567015909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44171860017168826562637/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40186521/50000000000000 : ℝ)*(base1) + (1774877833/100000000000000 : ℝ)*(base19) + (111764479/6250000000000 : ℝ)*(base23) + (46489653/20000000000000 : ℝ)*(upper3) + (57137191/25000000000000 : ℝ)*(upper5) + (71821244047097/10000000000000 : ℝ)*(major0) + (71821244047097/10000000000000 : ℝ)*(major1) + (71821244047097/10000000000000 : ℝ)*(major2) + (506518980325143/50000000000000 : ℝ)*(sp0) + (202608522497631/20000000000000 : ℝ)*(sp1) + (253260649783581/25000000000000 : ℝ)*(sp2) + (52922168570937/12500000000000 : ℝ)*(sp3) + (6507088743/100000000000000 : ℝ)*(sp4) + (1385078171/50000000000000 : ℝ)*(sp7) + (423380199096879/100000000000000 : ℝ)*(f.failure) + (253261096841497/25000000000000 : ℝ)*(f.sum) + (24102567984121/10000000000000000000000000000 : ℝ)*base66 + (124767556125879/20000000000000000000000000000 : ℝ)*base67 + (157214523854121/20000000000000000000000000000 : ℝ)*base70 + (64663792394121/20000000000000000000000000000 : ℝ)*base72 + (31288119425879/10000000000000000000000000000 : ℝ)*base73 + (100735865614121/20000000000000000000000000000 : ℝ)*base76 + (28474792725879/20000000000000000000000000000 : ℝ)*base77 + (78273349594121/20000000000000000000000000000 : ℝ)*base80 + (60499763394121/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (14466029/5000000000000000000000 : ℝ)*base89 + (14466029/5000000000000000000000 : ℝ)*base91 + (14466029/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116294528964209907280683/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10795003/1000000000000 : ℝ)*(base19) + (135162497/10000000000000 : ℝ)*(base23) + (415814267/100000000000000 : ℝ)*(base39) + (3774289/2500000000000 : ℝ)*(upper3) + (54831099/12500000000000 : ℝ)*(upper5) + (378798507686823/50000000000000 : ℝ)*(major0) + (378798507686823/50000000000000 : ℝ)*(major1) + (378798299779689/50000000000000 : ℝ)*(major2) + (341362977/10000000000000 : ℝ)*(sp1) + (2764022791/100000000000000 : ℝ)*(sp2) + (1068596384788507/100000000000000 : ℝ)*(sp4) + (1068591891658437/100000000000000 : ℝ)*(sp5) + (267148171238753/25000000000000 : ℝ)*(sp6) + (22329853754257/5000000000000 : ℝ)*(sp7) + (22329853754257/5000000000000 : ℝ)*(f.failure) + (534298400301387/50000000000000 : ℝ)*(f.sum) + (4093197642451/6250000000000000000000000000 : ℝ)*base66 + (151944467177223/100000000000000000000000000000 : ℝ)*base67 + (933207527656439/100000000000000000000000000000 : ℝ)*base70 + (69775010277223/100000000000000000000000000000 : ℝ)*base71 + (7382474992451/6250000000000000000000000000 : ℝ)*base74 + (774155579956439/100000000000000000000000000000 : ℝ)*base76 + (515390265243561/100000000000000000000000000000 : ℝ)*base77 + (752953447143561/100000000000000000000000000000 : ℝ)*base79 + (313600132006439/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (98707/250000000000000000000 : ℝ)*base89 + (98707/250000000000000000000 : ℝ)*base91 + (2598707/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1590_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1787/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3089/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1590_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1590_s1_0 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1736964851/10000000000 : ℝ)*x 0 + (5549758811/10000000000 : ℝ)*x 1 + (1276739169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1736964851/10000000000 : ℝ)^4679 ≤ (10636719919053/100000000000000 : ℝ)^3655 := by
    have hnat : (1736964851 : ℕ)^4679*100000000000000^3655 ≤ 10636719919053^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736964851 10000000000 10636719919053 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5549758811/10000000000 : ℝ)^4679 ≤ (47057503191837/100000000000000 : ℝ)^3655 := by
    have hnat : (5549758811 : ℕ)^4679*100000000000000^3655 ≤ 47057503191837^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549758811 10000000000 47057503191837 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1276739169/2500000000 : ℝ)^4679 ≤ (21152888435081/50000000000000 : ℝ)^3655 := by
    have hnat : (1276739169 : ℕ)^4679*50000000000000^3655 ≤ 21152888435081^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276739169 2500000000 21152888435081 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1736964851/10000000000 : ℝ), (5549758811/10000000000 : ℝ), (1276739169/2500000000 : ℝ)] ![(10636719919053/100000000000000 : ℝ), (47057503191837/100000000000000 : ℝ), (21152888435081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1736964851/10000000000 : ℝ)|^4679 ≤ (10636719919053/100000000000000 : ℝ)^3655
        have hw : |(-1736964851/10000000000 : ℝ)|=(1736964851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5549758811/10000000000 : ℝ)|^4679 ≤ (47057503191837/100000000000000 : ℝ)^3655
        have hw : |(5549758811/10000000000 : ℝ)|=(5549758811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1276739169/2500000000 : ℝ)|^4679 ≤ (21152888435081/50000000000000 : ℝ)^3655
        have hw : |(1276739169/2500000000 : ℝ)|=(1276739169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s1_1 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378107707/10000000000 : ℝ)*x 0 + (-393875843/2000000000 : ℝ)*x 1 + (1276739137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378107707/10000000000 : ℝ)^4679 ≤ (45202404238879/100000000000000 : ℝ)^3655 := by
    have hnat : (5378107707 : ℕ)^4679*100000000000000^3655 ≤ 45202404238879^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378107707 10000000000 45202404238879 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393875843/2000000000 : ℝ)^4679 ≤ (6245910120783/50000000000000 : ℝ)^3655 := by
    have hnat : (393875843 : ℕ)^4679*50000000000000^3655 ≤ 6245910120783^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393875843 2000000000 6245910120783 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1276739137/2500000000 : ℝ)^4679 ≤ (21152887756373/50000000000000 : ℝ)^3655 := by
    have hnat : (1276739137 : ℕ)^4679*50000000000000^3655 ≤ 21152887756373^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276739137 2500000000 21152887756373 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378107707/10000000000 : ℝ), (-393875843/2000000000 : ℝ), (1276739137/2500000000 : ℝ)] ![(45202404238879/100000000000000 : ℝ), (6245910120783/50000000000000 : ℝ), (21152887756373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378107707/10000000000 : ℝ)|^4679 ≤ (45202404238879/100000000000000 : ℝ)^3655
        have hw : |(5378107707/10000000000 : ℝ)|=(5378107707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393875843/2000000000 : ℝ)|^4679 ≤ (6245910120783/50000000000000 : ℝ)^3655
        have hw : |(-393875843/2000000000 : ℝ)|=(393875843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1276739137/2500000000 : ℝ)|^4679 ≤ (21152887756373/50000000000000 : ℝ)^3655
        have hw : |(1276739137/2500000000 : ℝ)|=(1276739137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s1_2 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378107509/10000000000 : ℝ)*x 0 + (5106956707/10000000000 : ℝ)*x 1 + (-492344817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378107509/10000000000 : ℝ)^4679 ≤ (45202402108471/100000000000000 : ℝ)^3655 := by
    have hnat : (5378107509 : ℕ)^4679*100000000000000^3655 ≤ 45202402108471^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378107509 10000000000 45202402108471 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5106956707/10000000000 : ℝ)^4679 ≤ (42305777198911/100000000000000 : ℝ)^3655 := by
    have hnat : (5106956707 : ℕ)^4679*100000000000000^3655 ≤ 42305777198911^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5106956707 10000000000 42305777198911 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492344817/2500000000 : ℝ)^4679 ≤ (3122955167983/25000000000000 : ℝ)^3655 := by
    have hnat : (492344817 : ℕ)^4679*25000000000000^3655 ≤ 3122955167983^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492344817 2500000000 3122955167983 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378107509/10000000000 : ℝ), (5106956707/10000000000 : ℝ), (-492344817/2500000000 : ℝ)] ![(45202402108471/100000000000000 : ℝ), (42305777198911/100000000000000 : ℝ), (3122955167983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378107509/10000000000 : ℝ)|^4679 ≤ (45202402108471/100000000000000 : ℝ)^3655
        have hw : |(5378107509/10000000000 : ℝ)|=(5378107509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5106956707/10000000000 : ℝ)|^4679 ≤ (42305777198911/100000000000000 : ℝ)^3655
        have hw : |(5106956707/10000000000 : ℝ)|=(5106956707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492344817/2500000000 : ℝ)|^4679 ≤ (3122955167983/25000000000000 : ℝ)^3655
        have hw : |(-492344817/2500000000 : ℝ)|=(492344817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s1_3 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215561589/10000000000 : ℝ)*x 0 + (185607793/500000000 : ℝ)*x 1 + (4771672783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215561589/10000000000 : ℝ)^4679 ≤ (2068394601659/6250000000000 : ℝ)^3655 := by
    have hnat : (4215561589 : ℕ)^4679*6250000000000^3655 ≤ 2068394601659^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215561589 10000000000 2068394601659 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185607793/500000000 : ℝ)^4679 ≤ (14061151703249/50000000000000 : ℝ)^3655 := by
    have hnat : (185607793 : ℕ)^4679*50000000000000^3655 ≤ 14061151703249^3655*500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185607793 500000000 14061151703249 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4771672783/10000000000 : ℝ)^4679 ≤ (38783382951267/100000000000000 : ℝ)^3655 := by
    have hnat : (4771672783 : ℕ)^4679*100000000000000^3655 ≤ 38783382951267^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771672783 10000000000 38783382951267 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215561589/10000000000 : ℝ), (185607793/500000000 : ℝ), (4771672783/10000000000 : ℝ)] ![(2068394601659/6250000000000 : ℝ), (14061151703249/50000000000000 : ℝ), (38783382951267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215561589/10000000000 : ℝ)|^4679 ≤ (2068394601659/6250000000000 : ℝ)^3655
        have hw : |(4215561589/10000000000 : ℝ)|=(4215561589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(185607793/500000000 : ℝ)|^4679 ≤ (14061151703249/50000000000000 : ℝ)^3655
        have hw : |(185607793/500000000 : ℝ)|=(185607793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4771672783/10000000000 : ℝ)|^4679 ≤ (38783382951267/100000000000000 : ℝ)^3655
        have hw : |(4771672783/10000000000 : ℝ)|=(4771672783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s1_4 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-347447/2000000 : ℝ)*x 0 + (2555984369/5000000000 : ℝ)*x 1 + (221786629/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (347447/2000000 : ℝ)^4679 ≤ (1329854721123/12500000000000 : ℝ)^3655 := by
    have hnat : (347447 : ℕ)^4679*12500000000000^3655 ≤ 1329854721123^3655*2000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347447 2000000 1329854721123 12500000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2555984369/5000000000 : ℝ)^4679 ≤ (42358936174347/100000000000000 : ℝ)^3655 := by
    have hnat : (2555984369 : ℕ)^4679*100000000000000^3655 ≤ 42358936174347^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555984369 5000000000 42358936174347 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221786629/400000000 : ℝ)^4679 ≤ (9400445209529/20000000000000 : ℝ)^3655 := by
    have hnat : (221786629 : ℕ)^4679*20000000000000^3655 ≤ 9400445209529^3655*400000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221786629 400000000 9400445209529 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-347447/2000000 : ℝ), (2555984369/5000000000 : ℝ), (221786629/400000000 : ℝ)] ![(1329854721123/12500000000000 : ℝ), (42358936174347/100000000000000 : ℝ), (9400445209529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-347447/2000000 : ℝ)|^4679 ≤ (1329854721123/12500000000000 : ℝ)^3655
        have hw : |(-347447/2000000 : ℝ)|=(347447/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2555984369/5000000000 : ℝ)|^4679 ≤ (42358936174347/100000000000000 : ℝ)^3655
        have hw : |(2555984369/5000000000 : ℝ)|=(2555984369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221786629/400000000 : ℝ)|^4679 ≤ (9400445209529/20000000000000 : ℝ)^3655
        have hw : |(221786629/400000000 : ℝ)|=(221786629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s1_5 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260696113/10000000000 : ℝ)*x 0 + (-1531672883/10000000000 : ℝ)*x 1 + (5544665227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260696113/10000000000 : ℝ)^4679 ≤ (43942981722707/100000000000000 : ℝ)^3655 := by
    have hnat : (5260696113 : ℕ)^4679*100000000000000^3655 ≤ 43942981722707^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260696113 10000000000 43942981722707 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1531672883/10000000000 : ℝ)^4679 ≤ (9054797622297/100000000000000 : ℝ)^3655 := by
    have hnat : (1531672883 : ℕ)^4679*100000000000000^3655 ≤ 9054797622297^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531672883 10000000000 9054797622297 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5544665227/10000000000 : ℝ)^4679 ≤ (47002220643363/100000000000000 : ℝ)^3655 := by
    have hnat : (5544665227 : ℕ)^4679*100000000000000^3655 ≤ 47002220643363^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544665227 10000000000 47002220643363 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260696113/10000000000 : ℝ), (-1531672883/10000000000 : ℝ), (5544665227/10000000000 : ℝ)] ![(43942981722707/100000000000000 : ℝ), (9054797622297/100000000000000 : ℝ), (47002220643363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260696113/10000000000 : ℝ)|^4679 ≤ (43942981722707/100000000000000 : ℝ)^3655
        have hw : |(5260696113/10000000000 : ℝ)|=(5260696113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1531672883/10000000000 : ℝ)|^4679 ≤ (9054797622297/100000000000000 : ℝ)^3655
        have hw : |(-1531672883/10000000000 : ℝ)|=(1531672883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5544665227/10000000000 : ℝ)|^4679 ≤ (47002220643363/100000000000000 : ℝ)^3655
        have hw : |(5544665227/10000000000 : ℝ)|=(5544665227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s1_6 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210427937/400000000 : ℝ)*x 0 + (693083061/1250000000 : ℝ)*x 1 + (-765835337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210427937/400000000 : ℝ)^4679 ≤ (43943006445631/100000000000000 : ℝ)^3655 := by
    have hnat : (210427937 : ℕ)^4679*100000000000000^3655 ≤ 43943006445631^3655*400000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210427937 400000000 43943006445631 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693083061/1250000000 : ℝ)^4679 ≤ (9400442524751/20000000000000 : ℝ)^3655 := by
    have hnat : (693083061 : ℕ)^4679*20000000000000^3655 ≤ 9400442524751^3655*1250000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693083061 1250000000 9400442524751 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (765835337/5000000000 : ℝ)^4679 ≤ (4527390452347/50000000000000 : ℝ)^3655 := by
    have hnat : (765835337 : ℕ)^4679*50000000000000^3655 ≤ 4527390452347^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765835337 5000000000 4527390452347 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210427937/400000000 : ℝ), (693083061/1250000000 : ℝ), (-765835337/5000000000 : ℝ)] ![(43943006445631/100000000000000 : ℝ), (9400442524751/20000000000000 : ℝ), (4527390452347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210427937/400000000 : ℝ)|^4679 ≤ (43943006445631/100000000000000 : ℝ)^3655
        have hw : |(210427937/400000000 : ℝ)|=(210427937/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(693083061/1250000000 : ℝ)|^4679 ≤ (9400442524751/20000000000000 : ℝ)^3655
        have hw : |(693083061/1250000000 : ℝ)|=(693083061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-765835337/5000000000 : ℝ)|^4679 ≤ (4527390452347/50000000000000 : ℝ)^3655
        have hw : |(-765835337/5000000000 : ℝ)|=(765835337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s1_7 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216208457/10000000000 : ℝ)*x 0 + (951935817/2000000000 : ℝ)*x 1 + (3724343157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216208457/10000000000 : ℝ)^4679 ≤ (33100814752881/100000000000000 : ℝ)^3655 := by
    have hnat : (4216208457 : ℕ)^4679*100000000000000^3655 ≤ 33100814752881^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216208457 10000000000 33100814752881 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (951935817/2000000000 : ℝ)^4679 ≤ (19329316444189/50000000000000 : ℝ)^3655 := by
    have hnat : (951935817 : ℕ)^4679*50000000000000^3655 ≤ 19329316444189^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951935817 2000000000 19329316444189 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3724343157/10000000000 : ℝ)^4679 ≤ (14120276175797/50000000000000 : ℝ)^3655 := by
    have hnat : (3724343157 : ℕ)^4679*50000000000000^3655 ≤ 14120276175797^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724343157 10000000000 14120276175797 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216208457/10000000000 : ℝ), (951935817/2000000000 : ℝ), (3724343157/10000000000 : ℝ)] ![(33100814752881/100000000000000 : ℝ), (19329316444189/50000000000000 : ℝ), (14120276175797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216208457/10000000000 : ℝ)|^4679 ≤ (33100814752881/100000000000000 : ℝ)^3655
        have hw : |(4216208457/10000000000 : ℝ)|=(4216208457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(951935817/2000000000 : ℝ)|^4679 ≤ (19329316444189/50000000000000 : ℝ)^3655
        have hw : |(951935817/2000000000 : ℝ)|=(951935817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3724343157/10000000000 : ℝ)|^4679 ≤ (14120276175797/50000000000000 : ℝ)^3655
        have hw : |(3724343157/10000000000 : ℝ)|=(3724343157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1590_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3089/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1787/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8747/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3089/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1787/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3089/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1787/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3089/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1787/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3089/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1787/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3089/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1787/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3089/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1787/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1787/50000 : ℝ) ^ (4675/1024 : ℝ) ≤ (24804405411617/100000000000000000000 : ℝ) := by
    have hpowers : (1787/50000 : ℝ)^4675 ≤ (24804405411617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1787 : ℕ)^4675*100000000000000000000^1024 ≤ 24804405411617^1024*50000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1787 50000 24804405411617 100000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1787/50000 : ℝ)) (X := (24804405411617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3089/12500 : ℝ) ^ (4675/1024 : ℝ) ≤ (33837142300846723/20000000000000000000 : ℝ) := by
    have hpowers : (3089/12500 : ℝ)^4675 ≤ (33837142300846723/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3089 : ℕ)^4675*20000000000000000000^1024 ≤ 33837142300846723^1024*12500^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3089 12500 33837142300846723 20000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3089/12500 : ℝ)) (X := (33837142300846723/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000024804405411617/50000000000000000000 : ℝ) ≤ (625000067913653/625000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (50000024804405411617/50000000000000000000 : ℝ)^1024 ≤ (625000067913653/625000000000000 : ℝ)^4675 := by
      have hnat : (50000024804405411617 : ℕ)^1024*625000000000000^4675 ≤ 625000067913653^4675*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000024804405411617 50000000000000000000 625000067913653 625000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000067913653/625000000000000 : ℝ)) (X := (50000024804405411617/50000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6260575657244352827/6250000000000000000 : ℝ) ≤ (2500925974312851/2500000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (6260575657244352827/6250000000000000000 : ℝ)^1024 ≤ (2500925974312851/2500000000000000 : ℝ)^4675 := by
      have hnat : (6260575657244352827 : ℕ)^1024*2500000000000000^4675 ≤ 2500925974312851^4675*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6260575657244352827 6250000000000000000 2500925974312851 2500000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500925974312851/2500000000000000 : ℝ)) (X := (6260575657244352827/6250000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10033837142300846723/10000000000000000000 : ℝ) ≤ (250185167697109/250000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (10033837142300846723/10000000000000000000 : ℝ)^1024 ≤ (250185167697109/250000000000000 : ℝ)^4675 := by
      have hnat : (10033837142300846723 : ℕ)^1024*250000000000000^4675 ≤ 250185167697109^4675*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10033837142300846723 10000000000000000000 250185167697109 250000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250185167697109/250000000000000 : ℝ)) (X := (10033837142300846723/10000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24804405411617/100000000000000000000 : ℝ) ≤ ((13209597204908524021/13211250000000000000 : ℝ)+2*(925702658239/528450000000000 : ℝ)*(1787/50000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (13209597204908524021/13211250000000000000 : ℝ)+2*(925702658239/528450000000000 : ℝ)*(1787/50000 : ℝ)=(625000067913653/625000000000000 : ℝ) by norm_num, show 1+2*(24804405411617/100000000000000000000 : ℝ)=(50000024804405411617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33837142300846723/20000000000000000000 : ℝ)+(24804405411617/100000000000000000000 : ℝ) ≤ ((13209597204908524021/13211250000000000000 : ℝ)+(925702658239/528450000000000 : ℝ)*((3089/12500 : ℝ)+(1787/50000 : ℝ)))^(4675/1024 : ℝ) := by
    rw [show (13209597204908524021/13211250000000000000 : ℝ)+(925702658239/528450000000000 : ℝ)*((3089/12500 : ℝ)+(1787/50000 : ℝ))=(2500925974312851/2500000000000000 : ℝ) by norm_num, show 1+(33837142300846723/20000000000000000000 : ℝ)+(24804405411617/100000000000000000000 : ℝ)=(6260575657244352827/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33837142300846723/20000000000000000000 : ℝ) ≤ ((13209597204908524021/13211250000000000000 : ℝ)+2*(925702658239/528450000000000 : ℝ)*(3089/12500 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (13209597204908524021/13211250000000000000 : ℝ)+2*(925702658239/528450000000000 : ℝ)*(3089/12500 : ℝ)=(250185167697109/250000000000000 : ℝ) by norm_num, show 1+2*(33837142300846723/20000000000000000000 : ℝ)=(10033837142300846723/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13209597204908524021/13211250000000000000 : ℝ)*(X 1 0+X 2 0)+(925702658239/528450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (1787/50000 : ℝ)) (hi := (3089/12500 : ℝ)) (c := (13209597204908524021/13211250000000000000 : ℝ)) (alpha := (925702658239/528450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13209597204908524021/13211250000000000000 : ℝ)*(X 0 1+X 2 1)+(925702658239/528450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (1787/50000 : ℝ)) (hi := (3089/12500 : ℝ)) (c := (13209597204908524021/13211250000000000000 : ℝ)) (alpha := (925702658239/528450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13209597204908524021/13211250000000000000 : ℝ)*(X 0 2+X 1 2)+(925702658239/528450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (1787/50000 : ℝ)) (hi := (3089/12500 : ℝ)) (c := (13209597204908524021/13211250000000000000 : ℝ)) (alpha := (925702658239/528450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1736964851/10000000000 : ℝ)*X 0 0+(5549758811/10000000000 : ℝ)*X 0 1+(1276739169/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378107707/10000000000 : ℝ)*X 1 0+(-393875843/2000000000 : ℝ)*X 1 1+(1276739137/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378107509/10000000000 : ℝ)*X 2 0+(5106956707/10000000000 : ℝ)*X 2 1+(-492344817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4215561589/10000000000 : ℝ)*X 0 0+(185607793/500000000 : ℝ)*X 0 1+(4771672783/10000000000 : ℝ)*X 0 2+(4215561589/10000000000 : ℝ)*X 1 0+(185607793/500000000 : ℝ)*X 1 1+(4771672783/10000000000 : ℝ)*X 1 2+(4215561589/10000000000 : ℝ)*X 2 0+(185607793/500000000 : ℝ)*X 2 1+(4771672783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-347447/2000000 : ℝ)*X 0 0+(2555984369/5000000000 : ℝ)*X 0 1+(221786629/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260696113/10000000000 : ℝ)*X 1 0+(-1531672883/10000000000 : ℝ)*X 1 1+(5544665227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210427937/400000000 : ℝ)*X 2 0+(693083061/1250000000 : ℝ)*X 2 1+(-765835337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216208457/10000000000 : ℝ)*X 0 0+(951935817/2000000000 : ℝ)*X 0 1+(3724343157/10000000000 : ℝ)*X 0 2+(4216208457/10000000000 : ℝ)*X 1 0+(951935817/2000000000 : ℝ)*X 1 1+(3724343157/10000000000 : ℝ)*X 1 2+(4216208457/10000000000 : ℝ)*X 2 0+(951935817/2000000000 : ℝ)*X 2 1+(3724343157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (445746292943636347720180977/55046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37323407/50000000000000 : ℝ)*(base1) + (435896937/25000000000000 : ℝ)*(base19) + (1660443769/100000000000000 : ℝ)*(base23) + (106257943/50000000000000 : ℝ)*(upper3) + (10532951/6250000000000 : ℝ)*(upper5) + (200138121790653/12500000000000 : ℝ)*(major0) + (200138121790653/12500000000000 : ℝ)*(major1) + (200138121790653/12500000000000 : ℝ)*(major2) + (2258358719208749/100000000000000 : ℝ)*(sp0) + (282296250696809/12500000000000 : ℝ)*(sp1) + (564592522179613/25000000000000 : ℝ)*(sp2) + (943831966055513/100000000000000 : ℝ)*(sp3) + (2620920057/20000000000000 : ℝ)*(sp4) + (588886667/10000000000000 : ℝ)*(sp7) + (235959482392249/25000000000000 : ℝ)*(f.failure) + (112918587458111/5000000000000 : ℝ)*(f.sum) + (14290636616749/4403750000000000000000000000 : ℝ)*base66 + (86057337748078527/27523437500000000000000000000000 : ℝ)*base68 + (162381778021735179/55046875000000000000000000000000 : ℝ)*base70 + (61698907080078527/27523437500000000000000000000000 : ℝ)*base72 + (36879626648863/8807500000000000000000000000 : ℝ)*base74 + (13430961796281049/13761718750000000000000000000000 : ℝ)*base75 + (118463254598609777/27523437500000000000000000000000 : ℝ)*base78 + (329500835930297679/55046875000000000000000000000000 : ℝ)*base80 + (41378886154771/17615000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (8514101/1250000000000000000000 : ℝ)*base90 + (8514101/1250000000000000000000 : ℝ)*base92 + (8514101/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (678619184865522114524390741/55046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (602746379/50000000000000 : ℝ)*(base19) + (342063471/12500000000000 : ℝ)*(base23) + (2047421/781250000000 : ℝ)*(upper3) + (912367/800000000000 : ℝ)*(lower4) + (185010351/50000000000000 : ℝ)*(upper5) + (409620165041357/25000000000000 : ℝ)*(major0) + (409620165041357/25000000000000 : ℝ)*(major1) + (409620165041357/25000000000000 : ℝ)*(major2) + (1826845137/50000000000000 : ℝ)*(sp1) + (2128771661/12500000000000 : ℝ)*(sp2) + (1155545163531357/50000000000000 : ℝ)*(sp4) + (1155542733939841/50000000000000 : ℝ)*(sp5) + (1155535280190829/50000000000000 : ℝ)*(sp6) + (120733822791751/12500000000000 : ℝ)*(sp7) + (120733822791751/12500000000000 : ℝ)*(f.failure) + (1155545163531357/50000000000000 : ℝ)*(f.sum) + (19547900969921/3302812500000000000000000000 : ℝ)*base66 + (1617582923112363503/330281250000000000000000000000000 : ℝ)*base68 + (3102990904808801003/330281250000000000000000000000000 : ℝ)*base70 + (4886728477366488503/330281250000000000000000000000000 : ℝ)*base72 + (15608417659501/13211250000000000000000000000 : ℝ)*base73 + (2155795247490176003/330281250000000000000000000000000 : ℝ)*base76 + (3025293228947801003/330281250000000000000000000000000 : ℝ)*base78 + (2948473939373988503/330281250000000000000000000000000 : ℝ)*base80 + (35518961516879/13211250000000000000000000000 : ℝ)*base82 + (7098101/625000000000000000000 : ℝ)*base89 + (7098101/625000000000000000000 : ℝ)*base91 + (7098101/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1590_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3089/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1787/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8747/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1590_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1590_s2_0 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438470507/2500000000 : ℝ)*x 0 + (85560719/156250000 : ℝ)*x 1 + (5169798459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438470507/2500000000 : ℝ)^4679 ≤ (336547525333/3125000000000 : ℝ)^3655 := by
    have hnat : (438470507 : ℕ)^4679*3125000000000^3655 ≤ 336547525333^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438470507 2500000000 336547525333 3125000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85560719/156250000 : ℝ)^4679 ≤ (46257131343637/100000000000000 : ℝ)^3655 := by
    have hnat : (85560719 : ℕ)^4679*100000000000000^3655 ≤ 46257131343637^3655*156250000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85560719 156250000 46257131343637 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169798459/10000000000 : ℝ)^4679 ≤ (42973347820653/100000000000000 : ℝ)^3655 := by
    have hnat : (5169798459 : ℕ)^4679*100000000000000^3655 ≤ 42973347820653^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169798459 10000000000 42973347820653 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438470507/2500000000 : ℝ), (85560719/156250000 : ℝ), (5169798459/10000000000 : ℝ)] ![(336547525333/3125000000000 : ℝ), (46257131343637/100000000000000 : ℝ), (42973347820653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438470507/2500000000 : ℝ)|^4679 ≤ (336547525333/3125000000000 : ℝ)^3655
        have hw : |(-438470507/2500000000 : ℝ)|=(438470507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85560719/156250000 : ℝ)|^4679 ≤ (46257131343637/100000000000000 : ℝ)^3655
        have hw : |(85560719/156250000 : ℝ)|=(85560719/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169798459/10000000000 : ℝ)|^4679 ≤ (42973347820653/100000000000000 : ℝ)^3655
        have hw : |(5169798459/10000000000 : ℝ)|=(5169798459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s2_1 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339759453/2500000000 : ℝ)*x 0 + (-1912188889/10000000000 : ℝ)*x 1 + (2584899243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339759453/2500000000 : ℝ)^4679 ≤ (1406166282989/3125000000000 : ℝ)^3655 := by
    have hnat : (1339759453 : ℕ)^4679*3125000000000^3655 ≤ 1406166282989^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339759453 2500000000 1406166282989 3125000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912188889/10000000000 : ℝ)^4679 ≤ (240586616427/2000000000000 : ℝ)^3655 := by
    have hnat : (1912188889 : ℕ)^4679*2000000000000^3655 ≤ 240586616427^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912188889 10000000000 240586616427 2000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584899243/5000000000 : ℝ)^4679 ≤ (8594669621593/20000000000000 : ℝ)^3655 := by
    have hnat : (2584899243 : ℕ)^4679*20000000000000^3655 ≤ 8594669621593^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584899243 5000000000 8594669621593 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339759453/2500000000 : ℝ), (-1912188889/10000000000 : ℝ), (2584899243/5000000000 : ℝ)] ![(1406166282989/3125000000000 : ℝ), (240586616427/2000000000000 : ℝ), (8594669621593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339759453/2500000000 : ℝ)|^4679 ≤ (1406166282989/3125000000000 : ℝ)^3655
        have hw : |(1339759453/2500000000 : ℝ)|=(1339759453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912188889/10000000000 : ℝ)|^4679 ≤ (240586616427/2000000000000 : ℝ)^3655
        have hw : |(-1912188889/10000000000 : ℝ)|=(1912188889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584899243/5000000000 : ℝ)|^4679 ≤ (8594669621593/20000000000000 : ℝ)^3655
        have hw : |(2584899243/5000000000 : ℝ)|=(2584899243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s2_2 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339759461/2500000000 : ℝ)*x 0 + (5169798427/10000000000 : ℝ)*x 1 + (-1912188923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339759461/2500000000 : ℝ)^4679 ≤ (22498660699807/50000000000000 : ℝ)^3655 := by
    have hnat : (1339759461 : ℕ)^4679*50000000000000^3655 ≤ 22498660699807^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339759461 2500000000 22498660699807 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169798427/10000000000 : ℝ)^4679 ≤ (21486673740067/50000000000000 : ℝ)^3655 := by
    have hnat : (5169798427 : ℕ)^4679*50000000000000^3655 ≤ 21486673740067^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169798427 10000000000 21486673740067 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1912188923/10000000000 : ℝ)^4679 ≤ (12029331095163/100000000000000 : ℝ)^3655 := by
    have hnat : (1912188923 : ℕ)^4679*100000000000000^3655 ≤ 12029331095163^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912188923 10000000000 12029331095163 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339759461/2500000000 : ℝ), (5169798427/10000000000 : ℝ), (-1912188923/10000000000 : ℝ)] ![(22498660699807/50000000000000 : ℝ), (21486673740067/50000000000000 : ℝ), (12029331095163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339759461/2500000000 : ℝ)|^4679 ≤ (22498660699807/50000000000000 : ℝ)^3655
        have hw : |(1339759461/2500000000 : ℝ)|=(1339759461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169798427/10000000000 : ℝ)|^4679 ≤ (21486673740067/50000000000000 : ℝ)^3655
        have hw : |(5169798427/10000000000 : ℝ)|=(5169798427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1912188923/10000000000 : ℝ)|^4679 ≤ (12029331095163/100000000000000 : ℝ)^3655
        have hw : |(-1912188923/10000000000 : ℝ)|=(1912188923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s2_3 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227973263/10000000000 : ℝ)*x 0 + (3874370459/10000000000 : ℝ)*x 1 + (4606762821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227973263/10000000000 : ℝ)^4679 ≤ (33219101653871/100000000000000 : ℝ)^3655 := by
    have hnat : (4227973263 : ℕ)^4679*100000000000000^3655 ≤ 33219101653871^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227973263 10000000000 33219101653871 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3874370459/10000000000 : ℝ)^4679 ≤ (7426255268611/25000000000000 : ℝ)^3655 := by
    have hnat : (3874370459 : ℕ)^4679*25000000000000^3655 ≤ 7426255268611^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3874370459 10000000000 7426255268611 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4606762821/10000000000 : ℝ)^4679 ≤ (1158621163949/3125000000000 : ℝ)^3655 := by
    have hnat : (4606762821 : ℕ)^4679*3125000000000^3655 ≤ 1158621163949^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606762821 10000000000 1158621163949 3125000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227973263/10000000000 : ℝ), (3874370459/10000000000 : ℝ), (4606762821/10000000000 : ℝ)] ![(33219101653871/100000000000000 : ℝ), (7426255268611/25000000000000 : ℝ), (1158621163949/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227973263/10000000000 : ℝ)|^4679 ≤ (33219101653871/100000000000000 : ℝ)^3655
        have hw : |(4227973263/10000000000 : ℝ)|=(4227973263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3874370459/10000000000 : ℝ)|^4679 ≤ (7426255268611/25000000000000 : ℝ)^3655
        have hw : |(3874370459/10000000000 : ℝ)|=(3874370459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4606762821/10000000000 : ℝ)|^4679 ≤ (1158621163949/3125000000000 : ℝ)^3655
        have hw : |(4606762821/10000000000 : ℝ)|=(4606762821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s2_4 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1753971173/10000000000 : ℝ)*x 0 + (2586101017/5000000000 : ℝ)*x 1 + (5473455761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1753971173/10000000000 : ℝ)^4679 ≤ (10770221558463/100000000000000 : ℝ)^3655 := by
    have hnat : (1753971173 : ℕ)^4679*100000000000000^3655 ≤ 10770221558463^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753971173 10000000000 10770221558463 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586101017/5000000000 : ℝ)^4679 ≤ (42998926445861/100000000000000 : ℝ)^3655 := by
    have hnat : (2586101017 : ℕ)^4679*100000000000000^3655 ≤ 42998926445861^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586101017 5000000000 42998926445861 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473455761/10000000000 : ℝ)^4679 ≤ (11557712995637/25000000000000 : ℝ)^3655 := by
    have hnat : (5473455761 : ℕ)^4679*25000000000000^3655 ≤ 11557712995637^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473455761 10000000000 11557712995637 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1753971173/10000000000 : ℝ), (2586101017/5000000000 : ℝ), (5473455761/10000000000 : ℝ)] ![(10770221558463/100000000000000 : ℝ), (42998926445861/100000000000000 : ℝ), (11557712995637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1753971173/10000000000 : ℝ)|^4679 ≤ (10770221558463/100000000000000 : ℝ)^3655
        have hw : |(-1753971173/10000000000 : ℝ)|=(1753971173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586101017/5000000000 : ℝ)|^4679 ≤ (42998926445861/100000000000000 : ℝ)^3655
        have hw : |(2586101017/5000000000 : ℝ)|=(2586101017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473455761/10000000000 : ℝ)|^4679 ≤ (11557712995637/25000000000000 : ℝ)^3655
        have hw : |(5473455761/10000000000 : ℝ)|=(5473455761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s2_5 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278050729/10000000000 : ℝ)*x 0 + (-402132893/2500000000 : ℝ)*x 1 + (547345589/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278050729/10000000000 : ℝ)^4679 ≤ (44128645623477/100000000000000 : ℝ)^3655 := by
    have hnat : (5278050729 : ℕ)^4679*100000000000000^3655 ≤ 44128645623477^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278050729 10000000000 44128645623477 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402132893/2500000000 : ℝ)^4679 ≤ (2410125245429/25000000000000 : ℝ)^3655 := by
    have hnat : (402132893 : ℕ)^4679*25000000000000^3655 ≤ 2410125245429^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402132893 2500000000 2410125245429 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547345589/1000000000 : ℝ)^4679 ≤ (2889428336087/6250000000000 : ℝ)^3655 := by
    have hnat : (547345589 : ℕ)^4679*6250000000000^3655 ≤ 2889428336087^3655*1000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547345589 1000000000 2889428336087 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278050729/10000000000 : ℝ), (-402132893/2500000000 : ℝ), (547345589/1000000000 : ℝ)] ![(44128645623477/100000000000000 : ℝ), (2410125245429/25000000000000 : ℝ), (2889428336087/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278050729/10000000000 : ℝ)|^4679 ≤ (44128645623477/100000000000000 : ℝ)^3655
        have hw : |(5278050729/10000000000 : ℝ)|=(5278050729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402132893/2500000000 : ℝ)|^4679 ≤ (2410125245429/25000000000000 : ℝ)^3655
        have hw : |(-402132893/2500000000 : ℝ)|=(402132893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547345589/1000000000 : ℝ)|^4679 ≤ (2889428336087/6250000000000 : ℝ)^3655
        have hw : |(547345589/1000000000 : ℝ)|=(547345589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s2_6 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278050873/10000000000 : ℝ)*x 0 + (5473455561/10000000000 : ℝ)*x 1 + (-321706367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278050873/10000000000 : ℝ)^4679 ≤ (8825729432947/20000000000000 : ℝ)^3655 := by
    have hnat : (5278050873 : ℕ)^4679*20000000000000^3655 ≤ 8825729432947^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278050873 10000000000 8825729432947 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473455561/10000000000 : ℝ)^4679 ≤ (46230849819999/100000000000000 : ℝ)^3655 := by
    have hnat : (5473455561 : ℕ)^4679*100000000000000^3655 ≤ 46230849819999^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473455561 10000000000 46230849819999 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321706367/2000000000 : ℝ)^4679 ≤ (4820251499789/50000000000000 : ℝ)^3655 := by
    have hnat : (321706367 : ℕ)^4679*50000000000000^3655 ≤ 4820251499789^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321706367 2000000000 4820251499789 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278050873/10000000000 : ℝ), (5473455561/10000000000 : ℝ), (-321706367/2000000000 : ℝ)] ![(8825729432947/20000000000000 : ℝ), (46230849819999/100000000000000 : ℝ), (4820251499789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278050873/10000000000 : ℝ)|^4679 ≤ (8825729432947/20000000000000 : ℝ)^3655
        have hw : |(5278050873/10000000000 : ℝ)|=(5278050873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473455561/10000000000 : ℝ)|^4679 ≤ (46230849819999/100000000000000 : ℝ)^3655
        have hw : |(5473455561/10000000000 : ℝ)|=(5473455561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321706367/2000000000 : ℝ)|^4679 ≤ (4820251499789/50000000000000 : ℝ)^3655
        have hw : |(-321706367/2000000000 : ℝ)|=(321706367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s2_7 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057046787/2500000000 : ℝ)*x 0 + (4601012149/10000000000 : ℝ)*x 1 + (3880185501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057046787/2500000000 : ℝ)^4679 ≤ (259541038847/781250000000 : ℝ)^3655 := by
    have hnat : (1057046787 : ℕ)^4679*781250000000^3655 ≤ 259541038847^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057046787 2500000000 259541038847 781250000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4601012149/10000000000 : ℝ)^4679 ≤ (9254159692797/25000000000000 : ℝ)^3655 := by
    have hnat : (4601012149 : ℕ)^4679*25000000000000^3655 ≤ 9254159692797^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601012149 10000000000 9254159692797 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3880185501/10000000000 : ℝ)^4679 ≤ (2976210824357/10000000000000 : ℝ)^3655 := by
    have hnat : (3880185501 : ℕ)^4679*10000000000000^3655 ≤ 2976210824357^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880185501 10000000000 2976210824357 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057046787/2500000000 : ℝ), (4601012149/10000000000 : ℝ), (3880185501/10000000000 : ℝ)] ![(259541038847/781250000000 : ℝ), (9254159692797/25000000000000 : ℝ), (2976210824357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057046787/2500000000 : ℝ)|^4679 ≤ (259541038847/781250000000 : ℝ)^3655
        have hw : |(1057046787/2500000000 : ℝ)|=(1057046787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4601012149/10000000000 : ℝ)|^4679 ≤ (9254159692797/25000000000000 : ℝ)^3655
        have hw : |(4601012149/10000000000 : ℝ)|=(4601012149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3880185501/10000000000 : ℝ)|^4679 ≤ (2976210824357/10000000000000 : ℝ)^3655
        have hw : |(3880185501/10000000000 : ℝ)|=(3880185501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1590_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2021/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8293/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8747/100000 : ℝ) ^ (4675/1024 : ℝ) ≤ (295231190875403/20000000000000000000 : ℝ) := by
    have hpowers : (8747/100000 : ℝ)^4675 ≤ (295231190875403/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8747 : ℕ)^4675*20000000000000000000^1024 ≤ 295231190875403^1024*100000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8747 100000 295231190875403 20000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8747/100000 : ℝ)) (X := (295231190875403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18121/100000 : ℝ) ^ (4675/1024 : ℝ) ≤ (41047131456398771/100000000000000000000 : ℝ) := by
    have hpowers : (18121/100000 : ℝ)^4675 ≤ (41047131456398771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18121 : ℕ)^4675*100000000000000000000^1024 ≤ 41047131456398771^1024*100000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18121 100000 41047131456398771 100000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18121/100000 : ℝ)) (X := (41047131456398771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000295231190875403/10000000000000000000 : ℝ) ≤ (5000032332968379/5000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (10000295231190875403/10000000000000000000 : ℝ)^1024 ≤ (5000032332968379/5000000000000000 : ℝ)^4675 := by
      have hnat : (10000295231190875403 : ℕ)^1024*5000000000000000^4675 ≤ 5000032332968379^4675*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000295231190875403 10000000000000000000 5000032332968379 5000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000032332968379/5000000000000000 : ℝ)) (X := (10000295231190875403/10000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021261643705387893/50000000000000000000 : ℝ) ≤ (5000465632276733/5000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (50021261643705387893/50000000000000000000 : ℝ)^1024 ≤ (5000465632276733/5000000000000000 : ℝ)^4675 := by
      have hnat : (50021261643705387893 : ℕ)^1024*5000000000000000^4675 ≤ 5000465632276733^4675*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021261643705387893 50000000000000000000 5000465632276733 5000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000465632276733/5000000000000000 : ℝ)) (X := (50021261643705387893/50000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041047131456398771/50000000000000000000 : ℝ) ≤ (5000898931585087/5000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (50041047131456398771/50000000000000000000 : ℝ)^1024 ≤ (5000898931585087/5000000000000000 : ℝ)^4675 := by
      have hnat : (50041047131456398771 : ℕ)^1024*5000000000000000^4675 ≤ 5000898931585087^4675*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041047131456398771 50000000000000000000 5000898931585087 5000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000898931585087/5000000000000000 : ℝ)) (X := (50041047131456398771/50000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(295231190875403/20000000000000000000 : ℝ) ≤ ((4686272295114523987/4687000000000000000 : ℝ)+2*(216649654177/234350000000000 : ℝ)*(8747/100000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (4686272295114523987/4687000000000000000 : ℝ)+2*(216649654177/234350000000000 : ℝ)*(8747/100000 : ℝ)=(5000032332968379/5000000000000000 : ℝ) by norm_num, show 1+2*(295231190875403/20000000000000000000 : ℝ)=(10000295231190875403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41047131456398771/100000000000000000000 : ℝ)+(295231190875403/20000000000000000000 : ℝ) ≤ ((4686272295114523987/4687000000000000000 : ℝ)+(216649654177/234350000000000 : ℝ)*((18121/100000 : ℝ)+(8747/100000 : ℝ)))^(4675/1024 : ℝ) := by
    rw [show (4686272295114523987/4687000000000000000 : ℝ)+(216649654177/234350000000000 : ℝ)*((18121/100000 : ℝ)+(8747/100000 : ℝ))=(5000465632276733/5000000000000000 : ℝ) by norm_num, show 1+(41047131456398771/100000000000000000000 : ℝ)+(295231190875403/20000000000000000000 : ℝ)=(50021261643705387893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41047131456398771/100000000000000000000 : ℝ) ≤ ((4686272295114523987/4687000000000000000 : ℝ)+2*(216649654177/234350000000000 : ℝ)*(18121/100000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (4686272295114523987/4687000000000000000 : ℝ)+2*(216649654177/234350000000000 : ℝ)*(18121/100000 : ℝ)=(5000898931585087/5000000000000000 : ℝ) by norm_num, show 1+2*(41047131456398771/100000000000000000000 : ℝ)=(50041047131456398771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4686272295114523987/4687000000000000000 : ℝ)*(X 1 0+X 2 0)+(216649654177/234350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (8747/100000 : ℝ)) (hi := (18121/100000 : ℝ)) (c := (4686272295114523987/4687000000000000000 : ℝ)) (alpha := (216649654177/234350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4686272295114523987/4687000000000000000 : ℝ)*(X 0 1+X 2 1)+(216649654177/234350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (8747/100000 : ℝ)) (hi := (18121/100000 : ℝ)) (c := (4686272295114523987/4687000000000000000 : ℝ)) (alpha := (216649654177/234350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4686272295114523987/4687000000000000000 : ℝ)*(X 0 2+X 1 2)+(216649654177/234350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (8747/100000 : ℝ)) (hi := (18121/100000 : ℝ)) (c := (4686272295114523987/4687000000000000000 : ℝ)) (alpha := (216649654177/234350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-438470507/2500000000 : ℝ)*X 0 0+(85560719/156250000 : ℝ)*X 0 1+(5169798459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339759453/2500000000 : ℝ)*X 1 0+(-1912188889/10000000000 : ℝ)*X 1 1+(2584899243/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339759461/2500000000 : ℝ)*X 2 0+(5169798427/10000000000 : ℝ)*X 2 1+(-1912188923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4227973263/10000000000 : ℝ)*X 0 0+(3874370459/10000000000 : ℝ)*X 0 1+(4606762821/10000000000 : ℝ)*X 0 2+(4227973263/10000000000 : ℝ)*X 1 0+(3874370459/10000000000 : ℝ)*X 1 1+(4606762821/10000000000 : ℝ)*X 1 2+(4227973263/10000000000 : ℝ)*X 2 0+(3874370459/10000000000 : ℝ)*X 2 1+(4606762821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1753971173/10000000000 : ℝ)*X 0 0+(2586101017/5000000000 : ℝ)*X 0 1+(5473455761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278050729/10000000000 : ℝ)*X 1 0+(-402132893/2500000000 : ℝ)*X 1 1+(547345589/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278050873/10000000000 : ℝ)*X 2 0+(5473455561/10000000000 : ℝ)*X 2 1+(-321706367/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1057046787/2500000000 : ℝ)*X 0 0+(4601012149/10000000000 : ℝ)*X 0 1+(3880185501/10000000000 : ℝ)*X 0 2+(1057046787/2500000000 : ℝ)*X 1 0+(4601012149/10000000000 : ℝ)*X 1 1+(3880185501/10000000000 : ℝ)*X 1 2+(1057046787/2500000000 : ℝ)*X 2 0+(4601012149/10000000000 : ℝ)*X 2 1+(3880185501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (361004208964491403949490051/46870000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1319034519/100000000000000 : ℝ)*(base19) + (1268329893/100000000000000 : ℝ)*(base23) + (18813709/50000000000000 : ℝ)*(lower2) + (40361451/20000000000000 : ℝ)*(upper3) + (63482861/50000000000000 : ℝ)*(upper5) + (1158117645211409/50000000000000 : ℝ)*(major0) + (1158117645211409/50000000000000 : ℝ)*(major1) + (2316235290422819/100000000000000 : ℝ)*(major2) + (3267054455697899/100000000000000 : ℝ)*(sp0) + (1633533881412621/50000000000000 : ℝ)*(sp1) + (3267067813529867/100000000000000 : ℝ)*(sp2) + (1365394373862379/100000000000000 : ℝ)*(sp3) + (7313080931/50000000000000 : ℝ)*(sp4) + (6868382001/100000000000000 : ℝ)*(sp7) + (68270062112219/5000000000000 : ℝ)*(f.failure) + (40838363523247/1250000000000 : ℝ)*(f.sum) + (225673609289/366171875000000000000000000 : ℝ)*base66 + (744885881932502317/234350000000000000000000000000000 : ℝ)*base68 + (2093317123378720647/468700000000000000000000000000000 : ℝ)*base70 + (3162427950534952317/234350000000000000000000000000000 : ℝ)*base72 + (109785274571929/23435000000000000000000000000 : ℝ)*base73 + (346031171523020647/468700000000000000000000000000000 : ℝ)*base76 + (1442411660858122317/234350000000000000000000000000000 : ℝ)*base78 + (4118707483222317/234350000000000000000000000000000 : ℝ)*base80 + (69673022222693/23435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (3640369/250000000000000000000 : ℝ)*base89 + (3640369/250000000000000000000 : ℝ)*base91 + (1140369/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4950260836259641773687663/1362500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96564167/50000000000000 : ℝ)*(base19) + (46491371/10000000000000 : ℝ)*(base23) + (28154267/50000000000000 : ℝ)*(upper3) + (47287151/50000000000000 : ℝ)*(lower4) + (588344409910231/25000000000000 : ℝ)*(major0) + (588344409910231/25000000000000 : ℝ)*(major1) + (588344409910231/25000000000000 : ℝ)*(major2) + (608686597/25000000000000 : ℝ)*(sp1) + (2567511669/100000000000000 : ℝ)*(sp2) + (60034239/100000000000000 : ℝ)*(sp3) + (165972940657167/5000000000000 : ℝ)*(sp4) + (1659728092634309/50000000000000 : ℝ)*(sp5) + (82986394517949/2500000000000 : ℝ)*(sp6) + (346824071249241/25000000000000 : ℝ)*(sp7) + (1387296345031203/100000000000000 : ℝ)*(f.failure) + (165972940657167/5000000000000 : ℝ)*(f.sum) + (29636132056319/23435000000000000000000000000 : ℝ)*base66 + (690293545107975997/117175000000000000000000000000000 : ℝ)*base67 + (250951438388574003/117175000000000000000000000000000 : ℝ)*base70 + (1222724885826225997/117175000000000000000000000000000 : ℝ)*base71 + (76471874773319/23435000000000000000000000000 : ℝ)*base74 + (492196817802974003/117175000000000000000000000000000 : ℝ)*base76 + (1198207758531075997/117175000000000000000000000000000 : ℝ)*base77 + (1469112806370950997/117175000000000000000000000000000 : ℝ)*base79 + (538786018833/2929375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2392247/5000000000000000000000 : ℝ)*base90 + (2392247/5000000000000000000000 : ℝ)*base92 + (2392247/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1590_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2021/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8293/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1590_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1590_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2021/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8293/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1590_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1590_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1590_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2021/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8293/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1590_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
