-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1337_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:22.411205+00:00
-- url     : https://prove2.me/submissions/b35d5ac5-d4bb-4bfd-aa22-d936ecfd0d13

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
theorem support_rectangle_w1337_s0_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-453026443/2500000000 : ℝ)*x 0 + (2999539503/5000000000 : ℝ)*x 1 + (4809714721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453026443/2500000000 : ℝ)^4297 ≤ (1061932121221/10000000000000 : ℝ)^3273 := by
    have hnat : (453026443 : ℕ)^4297*10000000000000^3273 ≤ 1061932121221^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453026443 2500000000 1061932121221 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2999539503/5000000000 : ℝ)^4297 ≤ (6390951349563/12500000000000 : ℝ)^3273 := by
    have hnat : (2999539503 : ℕ)^4297*12500000000000^3273 ≤ 6390951349563^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999539503 5000000000 6390951349563 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4809714721/10000000000 : ℝ)^4297 ≤ (9563266991387/25000000000000 : ℝ)^3273 := by
    have hnat : (4809714721 : ℕ)^4297*25000000000000^3273 ≤ 9563266991387^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809714721 10000000000 9563266991387 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453026443/2500000000 : ℝ), (2999539503/5000000000 : ℝ), (4809714721/10000000000 : ℝ)] ![(1061932121221/10000000000000 : ℝ), (6390951349563/12500000000000 : ℝ), (9563266991387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453026443/2500000000 : ℝ)|^4297 ≤ (1061932121221/10000000000000 : ℝ)^3273
        have hw : |(-453026443/2500000000 : ℝ)|=(453026443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2999539503/5000000000 : ℝ)|^4297 ≤ (6390951349563/12500000000000 : ℝ)^3273
        have hw : |(2999539503/5000000000 : ℝ)|=(2999539503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4809714721/10000000000 : ℝ)|^4297 ≤ (9563266991387/25000000000000 : ℝ)^3273
        have hw : |(4809714721/10000000000 : ℝ)|=(4809714721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s0_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2751186331/5000000000 : ℝ)*x 0 + (-2488380991/10000000000 : ℝ)*x 1 + (4809715103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751186331/5000000000 : ℝ)^4297 ≤ (45643374285577/100000000000000 : ℝ)^3273 := by
    have hnat : (2751186331 : ℕ)^4297*100000000000000^3273 ≤ 45643374285577^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751186331 5000000000 45643374285577 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2488380991/10000000000 : ℝ)^4297 ≤ (16103553739123/100000000000000 : ℝ)^3273 := by
    have hnat : (2488380991 : ℕ)^4297*100000000000000^3273 ≤ 16103553739123^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488380991 10000000000 16103553739123 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4809715103/10000000000 : ℝ)^4297 ≤ (4781633994279/12500000000000 : ℝ)^3273 := by
    have hnat : (4809715103 : ℕ)^4297*12500000000000^3273 ≤ 4781633994279^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809715103 10000000000 4781633994279 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751186331/5000000000 : ℝ), (-2488380991/10000000000 : ℝ), (4809715103/10000000000 : ℝ)] ![(45643374285577/100000000000000 : ℝ), (16103553739123/100000000000000 : ℝ), (4781633994279/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751186331/5000000000 : ℝ)|^4297 ≤ (45643374285577/100000000000000 : ℝ)^3273
        have hw : |(2751186331/5000000000 : ℝ)|=(2751186331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2488380991/10000000000 : ℝ)|^4297 ≤ (16103553739123/100000000000000 : ℝ)^3273
        have hw : |(-2488380991/10000000000 : ℝ)|=(2488380991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4809715103/10000000000 : ℝ)|^4297 ≤ (4781633994279/12500000000000 : ℝ)^3273
        have hw : |(4809715103/10000000000 : ℝ)|=(4809715103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s0_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2751186137/5000000000 : ℝ)*x 0 + (4809715017/10000000000 : ℝ)*x 1 + (-497676319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751186137/5000000000 : ℝ)^4297 ≤ (45643370060071/100000000000000 : ℝ)^3273 := by
    have hnat : (2751186137 : ℕ)^4297*100000000000000^3273 ≤ 45643370060071^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751186137 5000000000 45643370060071 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4809715017/10000000000 : ℝ)^4297 ≤ (298852117627/781250000000 : ℝ)^3273 := by
    have hnat : (4809715017 : ℕ)^4297*781250000000^3273 ≤ 298852117627^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809715017 10000000000 298852117627 781250000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497676319/2000000000 : ℝ)^4297 ≤ (8051779435411/50000000000000 : ℝ)^3273 := by
    have hnat : (497676319 : ℕ)^4297*50000000000000^3273 ≤ 8051779435411^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497676319 2000000000 8051779435411 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751186137/5000000000 : ℝ), (4809715017/10000000000 : ℝ), (-497676319/2000000000 : ℝ)] ![(45643370060071/100000000000000 : ℝ), (298852117627/781250000000 : ℝ), (8051779435411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751186137/5000000000 : ℝ)|^4297 ≤ (45643370060071/100000000000000 : ℝ)^3273
        have hw : |(2751186137/5000000000 : ℝ)|=(2751186137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4809715017/10000000000 : ℝ)|^4297 ≤ (298852117627/781250000000 : ℝ)^3273
        have hw : |(4809715017/10000000000 : ℝ)|=(4809715017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497676319/2000000000 : ℝ)|^4297 ≤ (8051779435411/50000000000000 : ℝ)^3273
        have hw : |(-497676319/2000000000 : ℝ)|=(497676319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s0_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26121851/62500000 : ℝ)*x 0 + (621363469/2000000000 : ℝ)*x 1 + (279667009/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26121851/62500000 : ℝ)^4297 ≤ (31811759916663/100000000000000 : ℝ)^3273 := by
    have hnat : (26121851 : ℕ)^4297*100000000000000^3273 ≤ 31811759916663^3273*62500000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26121851 62500000 31811759916663 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621363469/2000000000 : ℝ)^4297 ≤ (538790830673/2500000000000 : ℝ)^3273 := by
    have hnat : (621363469 : ℕ)^4297*2500000000000^3273 ≤ 538790830673^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621363469 2000000000 538790830673 2500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279667009/500000000 : ℝ)^4297 ≤ (46636606829737/100000000000000 : ℝ)^3273 := by
    have hnat : (279667009 : ℕ)^4297*100000000000000^3273 ≤ 46636606829737^3273*500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279667009 500000000 46636606829737 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26121851/62500000 : ℝ), (621363469/2000000000 : ℝ), (279667009/500000000 : ℝ)] ![(31811759916663/100000000000000 : ℝ), (538790830673/2500000000000 : ℝ), (46636606829737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26121851/62500000 : ℝ)|^4297 ≤ (31811759916663/100000000000000 : ℝ)^3273
        have hw : |(26121851/62500000 : ℝ)|=(26121851/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621363469/2000000000 : ℝ)|^4297 ≤ (538790830673/2500000000000 : ℝ)^3273
        have hw : |(621363469/2000000000 : ℝ)|=(621363469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279667009/500000000 : ℝ)|^4297 ≤ (46636606829737/100000000000000 : ℝ)^3273
        have hw : |(279667009/500000000 : ℝ)|=(279667009/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s0_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-363317727/2000000000 : ℝ)*x 0 + (4840335229/10000000000 : ℝ)*x 1 + (2983682767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363317727/2000000000 : ℝ)^4297 ≤ (10653824141439/100000000000000 : ℝ)^3273 := by
    have hnat : (363317727 : ℕ)^4297*100000000000000^3273 ≤ 10653824141439^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363317727 2000000000 10653824141439 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4840335229/10000000000 : ℝ)^4297 ≤ (2410819528981/6250000000000 : ℝ)^3273 := by
    have hnat : (4840335229 : ℕ)^4297*6250000000000^3273 ≤ 2410819528981^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840335229 10000000000 2410819528981 6250000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2983682767/5000000000 : ℝ)^4297 ≤ (50773063376927/100000000000000 : ℝ)^3273 := by
    have hnat : (2983682767 : ℕ)^4297*100000000000000^3273 ≤ 50773063376927^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983682767 5000000000 50773063376927 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-363317727/2000000000 : ℝ), (4840335229/10000000000 : ℝ), (2983682767/5000000000 : ℝ)] ![(10653824141439/100000000000000 : ℝ), (2410819528981/6250000000000 : ℝ), (50773063376927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-363317727/2000000000 : ℝ)|^4297 ≤ (10653824141439/100000000000000 : ℝ)^3273
        have hw : |(-363317727/2000000000 : ℝ)|=(363317727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4840335229/10000000000 : ℝ)|^4297 ≤ (2410819528981/6250000000000 : ℝ)^3273
        have hw : |(4840335229/10000000000 : ℝ)|=(4840335229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2983682767/5000000000 : ℝ)|^4297 ≤ (50773063376927/100000000000000 : ℝ)^3273
        have hw : |(2983682767/5000000000 : ℝ)|=(2983682767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s0_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589132111/5000000000 : ℝ)*x 0 + (-1330731477/10000000000 : ℝ)*x 1 + (5967365351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589132111/5000000000 : ℝ)^4297 ≤ (42146651132329/100000000000000 : ℝ)^3273 := by
    have hnat : (2589132111 : ℕ)^4297*100000000000000^3273 ≤ 42146651132329^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589132111 5000000000 42146651132329 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1330731477/10000000000 : ℝ)^4297 ≤ (7080287521437/100000000000000 : ℝ)^3273 := by
    have hnat : (1330731477 : ℕ)^4297*100000000000000^3273 ≤ 7080287521437^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330731477 10000000000 7080287521437 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5967365351/10000000000 : ℝ)^4297 ≤ (50773061332737/100000000000000 : ℝ)^3273 := by
    have hnat : (5967365351 : ℕ)^4297*100000000000000^3273 ≤ 50773061332737^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5967365351 10000000000 50773061332737 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589132111/5000000000 : ℝ), (-1330731477/10000000000 : ℝ), (5967365351/10000000000 : ℝ)] ![(42146651132329/100000000000000 : ℝ), (7080287521437/100000000000000 : ℝ), (50773061332737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589132111/5000000000 : ℝ)|^4297 ≤ (42146651132329/100000000000000 : ℝ)^3273
        have hw : |(2589132111/5000000000 : ℝ)|=(2589132111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1330731477/10000000000 : ℝ)|^4297 ≤ (7080287521437/100000000000000 : ℝ)^3273
        have hw : |(-1330731477/10000000000 : ℝ)|=(1330731477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5967365351/10000000000 : ℝ)|^4297 ≤ (50773061332737/100000000000000 : ℝ)^3273
        have hw : |(5967365351/10000000000 : ℝ)|=(5967365351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s0_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589132113/5000000000 : ℝ)*x 0 + (2983682761/5000000000 : ℝ)*x 1 + (-1330731197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589132113/5000000000 : ℝ)^4297 ≤ (1317082849221/3125000000000 : ℝ)^3273 := by
    have hnat : (2589132113 : ℕ)^4297*3125000000000^3273 ≤ 1317082849221^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589132113 5000000000 1317082849221 3125000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2983682761/5000000000 : ℝ)^4297 ≤ (25386531621441/50000000000000 : ℝ)^3273 := by
    have hnat : (2983682761 : ℕ)^4297*50000000000000^3273 ≤ 25386531621441^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983682761 5000000000 25386531621441 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1330731197/10000000000 : ℝ)^4297 ≤ (7080285565577/100000000000000 : ℝ)^3273 := by
    have hnat : (1330731197 : ℕ)^4297*100000000000000^3273 ≤ 7080285565577^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330731197 10000000000 7080285565577 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589132113/5000000000 : ℝ), (2983682761/5000000000 : ℝ), (-1330731197/10000000000 : ℝ)] ![(1317082849221/3125000000000 : ℝ), (25386531621441/50000000000000 : ℝ), (7080285565577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589132113/5000000000 : ℝ)|^4297 ≤ (1317082849221/3125000000000 : ℝ)^3273
        have hw : |(2589132113/5000000000 : ℝ)|=(2589132113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2983682761/5000000000 : ℝ)|^4297 ≤ (25386531621441/50000000000000 : ℝ)^3273
        have hw : |(2983682761/5000000000 : ℝ)|=(2983682761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1330731197/10000000000 : ℝ)|^4297 ≤ (7080285565577/100000000000000 : ℝ)^3273
        have hw : |(-1330731197/10000000000 : ℝ)|=(1330731197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s0_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (837773329/2000000000 : ℝ)*x 0 + (5529324789/10000000000 : ℝ)*x 1 + (634623581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837773329/2000000000 : ℝ)^4297 ≤ (31905429242667/100000000000000 : ℝ)^3273 := by
    have hnat : (837773329 : ℕ)^4297*100000000000000^3273 ≤ 31905429242667^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837773329 2000000000 31905429242667 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529324789/10000000000 : ℝ)^4297 ≤ (4593712058957/10000000000000 : ℝ)^3273 := by
    have hnat : (5529324789 : ℕ)^4297*10000000000000^3273 ≤ 4593712058957^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529324789 10000000000 4593712058957 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634623581/2000000000 : ℝ)^4297 ≤ (11078725075887/50000000000000 : ℝ)^3273 := by
    have hnat : (634623581 : ℕ)^4297*50000000000000^3273 ≤ 11078725075887^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634623581 2000000000 11078725075887 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837773329/2000000000 : ℝ), (5529324789/10000000000 : ℝ), (634623581/2000000000 : ℝ)] ![(31905429242667/100000000000000 : ℝ), (4593712058957/10000000000000 : ℝ), (11078725075887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837773329/2000000000 : ℝ)|^4297 ≤ (31905429242667/100000000000000 : ℝ)^3273
        have hw : |(837773329/2000000000 : ℝ)|=(837773329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529324789/10000000000 : ℝ)|^4297 ≤ (4593712058957/10000000000000 : ℝ)^3273
        have hw : |(5529324789/10000000000 : ℝ)|=(5529324789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634623581/2000000000 : ℝ)|^4297 ≤ (11078725075887/50000000000000 : ℝ)^3273
        have hw : |(634623581/2000000000 : ℝ)|=(634623581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26907/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (537/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^537 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^537*1^128 ≤ 0^128*1^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (537/128 : ℝ) ≤ (2140510228017190067/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^537 ≤ (2140510228017190067/100000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^537*100000000000000000000^128 ≤ 2140510228017190067^128*5^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2140510228017190067 100000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2140510228017190067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^537 := by
      have hnat : (1 : ℕ)^128*1^537 ≤ 1^537*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (102140510228017190067/100000000000000000000 : ℝ) ≤ (5025305362012841/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (102140510228017190067/100000000000000000000 : ℝ)^128 ≤ (5025305362012841/5000000000000000 : ℝ)^537 := by
      have hnat : (102140510228017190067 : ℕ)^128*5000000000000000^537 ≤ 5025305362012841^537*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102140510228017190067 100000000000000000000 5025305362012841 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025305362012841/5000000000000000 : ℝ)) (X := (102140510228017190067/100000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (52140510228017190067/50000000000000000000 : ℝ) ≤ (2525305362012841/2500000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (52140510228017190067/50000000000000000000 : ℝ)^128 ≤ (2525305362012841/2500000000000000 : ℝ)^537 := by
      have hnat : (52140510228017190067 : ℕ)^128*2500000000000000^537 ≤ 2525305362012841^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52140510228017190067 50000000000000000000 2525305362012841 2500000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2525305362012841/2500000000000000 : ℝ)) (X := (52140510228017190067/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25305362012841/2000000000000000 : ℝ)*(0 : ℝ))^(537/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(25305362012841/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2140510228017190067/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25305362012841/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(537/128 : ℝ) := by
    rw [show (1 : ℝ)+(25305362012841/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5025305362012841/5000000000000000 : ℝ) by norm_num, show 1+(2140510228017190067/100000000000000000000 : ℝ)+(0 : ℝ)=(102140510228017190067/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2140510228017190067/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25305362012841/2000000000000000 : ℝ)*(2/5 : ℝ))^(537/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(25305362012841/2000000000000000 : ℝ)*(2/5 : ℝ)=(2525305362012841/2500000000000000 : ℝ) by norm_num, show 1+2*(2140510228017190067/100000000000000000000 : ℝ)=(52140510228017190067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25305362012841/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25305362012841/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25305362012841/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25305362012841/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25305362012841/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25305362012841/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-453026443/2500000000 : ℝ)*X 0 0+(2999539503/5000000000 : ℝ)*X 0 1+(4809714721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2751186331/5000000000 : ℝ)*X 1 0+(-2488380991/10000000000 : ℝ)*X 1 1+(4809715103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2751186137/5000000000 : ℝ)*X 2 0+(4809715017/10000000000 : ℝ)*X 2 1+(-497676319/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((26121851/62500000 : ℝ)*X 0 0+(621363469/2000000000 : ℝ)*X 0 1+(279667009/500000000 : ℝ)*X 0 2+(26121851/62500000 : ℝ)*X 1 0+(621363469/2000000000 : ℝ)*X 1 1+(279667009/500000000 : ℝ)*X 1 2+(26121851/62500000 : ℝ)*X 2 0+(621363469/2000000000 : ℝ)*X 2 1+(279667009/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-363317727/2000000000 : ℝ)*X 0 0+(4840335229/10000000000 : ℝ)*X 0 1+(2983682767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589132111/5000000000 : ℝ)*X 1 0+(-1330731477/10000000000 : ℝ)*X 1 1+(5967365351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589132113/5000000000 : ℝ)*X 2 0+(2983682761/5000000000 : ℝ)*X 2 1+(-1330731197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((837773329/2000000000 : ℝ)*X 0 0+(5529324789/10000000000 : ℝ)*X 0 1+(634623581/2000000000 : ℝ)*X 0 2+(837773329/2000000000 : ℝ)*X 1 0+(5529324789/10000000000 : ℝ)*X 1 1+(634623581/2000000000 : ℝ)*X 1 2+(837773329/2000000000 : ℝ)*X 2 0+(5529324789/10000000000 : ℝ)*X 2 1+(634623581/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9311517275553334657143/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32103579/50000000000000 : ℝ)*(base1) + (11014881/50000000000000 : ℝ)*(base16) + (559465379/100000000000000 : ℝ)*(base19) + (261103457/50000000000000 : ℝ)*(base23) + (49566941/50000000000000 : ℝ)*(upper3) + (24859174610059/4000000000000 : ℝ)*(major0) + (24859174610059/4000000000000 : ℝ)*(major1) + (24859174610059/4000000000000 : ℝ)*(major2) + (840787481985367/100000000000000 : ℝ)*(sp0) + (210197101860257/25000000000000 : ℝ)*(sp1) + (105098558341157/12500000000000 : ℝ)*(sp2) + (402168680938129/100000000000000 : ℝ)*(sp3) + (1571157961/100000000000000 : ℝ)*(sp4) + (114853189/12500000000000 : ℝ)*(sp7) + (402169663970799/100000000000000 : ℝ)*(f.failure) + (84078898893617/10000000000000 : ℝ)*(f.sum) + (9128244483619/4000000000000000000000000000 : ℝ)*base65 + (28600696184381/8000000000000000000000000000 : ℝ)*base68 + (12585029120381/8000000000000000000000000000 : ℝ)*base70 + (8583058439619/8000000000000000000000000000 : ℝ)*base71 + (4652737132381/4000000000000000000000000000 : ℝ)*base74 + (43048234055619/8000000000000000000000000000 : ℝ)*base75 + (9905685575619/8000000000000000000000000000 : ℝ)*base77 + (29684088832381/8000000000000000000000000000 : ℝ)*base80 + (7500436727619/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10332037/10000000000000000000000 : ℝ)*base90 + (10332037/10000000000000000000000 : ℝ)*base92 + (10332037/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112896517467136886737869/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37244227/4000000000000 : ℝ)*(base19) + (1002692637/100000000000000 : ℝ)*(base23) + (31431769/50000000000000 : ℝ)*(base39) + (58050121/50000000000000 : ℝ)*(upper3) + (65119481/50000000000000 : ℝ)*(upper5) + (13116982875493/2000000000000 : ℝ)*(major0) + (13116982875493/2000000000000 : ℝ)*(major1) + (81981135113889/12500000000000 : ℝ)*(major2) + (210031747/10000000000000 : ℝ)*(sp1) + (2200473/97656250000 : ℝ)*(sp2) + (22182178829791/2500000000000 : ℝ)*(sp4) + (177456824353699/20000000000000 : ℝ)*(sp5) + (221820990019547/25000000000000 : ℝ)*(sp6) + (424410920965427/100000000000000 : ℝ)*(sp7) + (424410920965427/100000000000000 : ℝ)*(f.failure) + (887287216055177/100000000000000 : ℝ)*(f.sum) + (85467584565079/100000000000000000000000000000 : ℝ)*base66 + (37044928873649/25000000000000000000000000000 : ℝ)*base67 + (49259854574387/4000000000000000000000000000 : ℝ)*base70 + (53690520676351/25000000000000000000000000000 : ℝ)*base72 + (40364484865079/100000000000000000000000000000 : ℝ)*base74 + (40568776154387/4000000000000000000000000000 : ℝ)*base76 + (5172004801613/4000000000000000000000000000 : ℝ)*base77 + (1654498113613/4000000000000000000000000000 : ℝ)*base79 + (11830505712387/2000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (54713999/10000000000000000000000 : ℝ)*base89 + (54713999/10000000000000000000000 : ℝ)*base91 + (54713999/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1337_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26907/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1337_s1_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1997643429/10000000000 : ℝ)*x 0 + (1411094751/2500000000 : ℝ)*x 1 + (2522799863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1997643429/10000000000 : ℝ)^4297 ≤ (12069132440737/100000000000000 : ℝ)^3273 := by
    have hnat : (1997643429 : ℕ)^4297*100000000000000^3273 ≤ 12069132440737^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997643429 10000000000 12069132440737 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1411094751/2500000000 : ℝ)^4297 ≤ (47196098868051/100000000000000 : ℝ)^3273 := by
    have hnat : (1411094751 : ℕ)^4297*100000000000000^3273 ≤ 47196098868051^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1411094751 2500000000 47196098868051 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2522799863/5000000000 : ℝ)^4297 ≤ (10183692168479/25000000000000 : ℝ)^3273 := by
    have hnat : (2522799863 : ℕ)^4297*25000000000000^3273 ≤ 10183692168479^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522799863 5000000000 10183692168479 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1997643429/10000000000 : ℝ), (1411094751/2500000000 : ℝ), (2522799863/5000000000 : ℝ)] ![(12069132440737/100000000000000 : ℝ), (47196098868051/100000000000000 : ℝ), (10183692168479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1997643429/10000000000 : ℝ)|^4297 ≤ (12069132440737/100000000000000 : ℝ)^3273
        have hw : |(-1997643429/10000000000 : ℝ)|=(1997643429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1411094751/2500000000 : ℝ)|^4297 ≤ (47196098868051/100000000000000 : ℝ)^3273
        have hw : |(1411094751/2500000000 : ℝ)|=(1411094751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2522799863/5000000000 : ℝ)|^4297 ≤ (10183692168479/25000000000000 : ℝ)^3273
        have hw : |(2522799863/5000000000 : ℝ)|=(2522799863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s1_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2703119441/5000000000 : ℝ)*x 0 + (-2317303063/10000000000 : ℝ)*x 1 + (504559957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703119441/5000000000 : ℝ)^4297 ≤ (44599304010387/100000000000000 : ℝ)^3273 := by
    have hnat : (2703119441 : ℕ)^4297*100000000000000^3273 ≤ 44599304010387^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703119441 5000000000 44599304010387 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2317303063/10000000000 : ℝ)^4297 ≤ (3666482238501/25000000000000 : ℝ)^3273 := by
    have hnat : (2317303063 : ℕ)^4297*25000000000000^3273 ≤ 3666482238501^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317303063 10000000000 3666482238501 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504559957/1000000000 : ℝ)^4297 ≤ (8146953404089/20000000000000 : ℝ)^3273 := by
    have hnat : (504559957 : ℕ)^4297*20000000000000^3273 ≤ 8146953404089^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504559957 1000000000 8146953404089 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703119441/5000000000 : ℝ), (-2317303063/10000000000 : ℝ), (504559957/1000000000 : ℝ)] ![(44599304010387/100000000000000 : ℝ), (3666482238501/25000000000000 : ℝ), (8146953404089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703119441/5000000000 : ℝ)|^4297 ≤ (44599304010387/100000000000000 : ℝ)^3273
        have hw : |(2703119441/5000000000 : ℝ)|=(2703119441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2317303063/10000000000 : ℝ)|^4297 ≤ (3666482238501/25000000000000 : ℝ)^3273
        have hw : |(-2317303063/10000000000 : ℝ)|=(2317303063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504559957/1000000000 : ℝ)|^4297 ≤ (8146953404089/20000000000000 : ℝ)^3273
        have hw : |(504559957/1000000000 : ℝ)|=(504559957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s1_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406238923/10000000000 : ℝ)*x 0 + (5045599347/10000000000 : ℝ)*x 1 + (-1158651647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406238923/10000000000 : ℝ)^4297 ≤ (44599304454441/100000000000000 : ℝ)^3273 := by
    have hnat : (5406238923 : ℕ)^4297*100000000000000^3273 ≤ 44599304454441^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406238923 10000000000 44599304454441 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5045599347/10000000000 : ℝ)^4297 ≤ (40734764656831/100000000000000 : ℝ)^3273 := by
    have hnat : (5045599347 : ℕ)^4297*100000000000000^3273 ≤ 40734764656831^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045599347 10000000000 40734764656831 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158651647/5000000000 : ℝ)^4297 ≤ (14665930873371/100000000000000 : ℝ)^3273 := by
    have hnat : (1158651647 : ℕ)^4297*100000000000000^3273 ≤ 14665930873371^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158651647 5000000000 14665930873371 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406238923/10000000000 : ℝ), (5045599347/10000000000 : ℝ), (-1158651647/5000000000 : ℝ)] ![(44599304454441/100000000000000 : ℝ), (40734764656831/100000000000000 : ℝ), (14665930873371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406238923/10000000000 : ℝ)|^4297 ≤ (44599304454441/100000000000000 : ℝ)^3273
        have hw : |(5406238923/10000000000 : ℝ)|=(5406238923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5045599347/10000000000 : ℝ)|^4297 ≤ (40734764656831/100000000000000 : ℝ)^3273
        have hw : |(5045599347/10000000000 : ℝ)|=(5045599347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1158651647/5000000000 : ℝ)|^4297 ≤ (14665930873371/100000000000000 : ℝ)^3273
        have hw : |(-1158651647/5000000000 : ℝ)|=(1158651647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s1_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107329983/250000000 : ℝ)*x 0 + (3709661153/10000000000 : ℝ)*x 1 + (4961489277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107329983/250000000 : ℝ)^4297 ≤ (131811070961/400000000000 : ℝ)^3273 := by
    have hnat : (107329983 : ℕ)^4297*400000000000^3273 ≤ 131811070961^3273*250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107329983 250000000 131811070961 400000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3709661153/10000000000 : ℝ)^4297 ≤ (3400203836491/12500000000000 : ℝ)^3273 := by
    have hnat : (3709661153 : ℕ)^4297*12500000000000^3273 ≤ 3400203836491^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709661153 10000000000 3400203836491 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4961489277/10000000000 : ℝ)^4297 ≤ (9961400388183/25000000000000 : ℝ)^3273 := by
    have hnat : (4961489277 : ℕ)^4297*25000000000000^3273 ≤ 9961400388183^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4961489277 10000000000 9961400388183 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107329983/250000000 : ℝ), (3709661153/10000000000 : ℝ), (4961489277/10000000000 : ℝ)] ![(131811070961/400000000000 : ℝ), (3400203836491/12500000000000 : ℝ), (9961400388183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107329983/250000000 : ℝ)|^4297 ≤ (131811070961/400000000000 : ℝ)^3273
        have hw : |(107329983/250000000 : ℝ)|=(107329983/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3709661153/10000000000 : ℝ)|^4297 ≤ (3400203836491/12500000000000 : ℝ)^3273
        have hw : |(3709661153/10000000000 : ℝ)|=(3709661153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4961489277/10000000000 : ℝ)|^4297 ≤ (9961400388183/25000000000000 : ℝ)^3273
        have hw : |(4961489277/10000000000 : ℝ)|=(4961489277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s1_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1998189173/10000000000 : ℝ)*x 0 + (1010628177/2000000000 : ℝ)*x 1 + (5636700163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998189173/10000000000 : ℝ)^4297 ≤ (12073461414549/100000000000000 : ℝ)^3273 := by
    have hnat : (1998189173 : ℕ)^4297*100000000000000^3273 ≤ 12073461414549^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998189173 10000000000 12073461414549 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010628177/2000000000 : ℝ)^4297 ≤ (4081471737249/10000000000000 : ℝ)^3273 := by
    have hnat : (1010628177 : ℕ)^4297*10000000000000^3273 ≤ 4081471737249^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010628177 2000000000 4081471737249 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5636700163/10000000000 : ℝ)^4297 ≤ (2355591060151/5000000000000 : ℝ)^3273 := by
    have hnat : (5636700163 : ℕ)^4297*5000000000000^3273 ≤ 2355591060151^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636700163 10000000000 2355591060151 5000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1998189173/10000000000 : ℝ), (1010628177/2000000000 : ℝ), (5636700163/10000000000 : ℝ)] ![(12073461414549/100000000000000 : ℝ), (4081471737249/10000000000000 : ℝ), (2355591060151/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1998189173/10000000000 : ℝ)|^4297 ≤ (12073461414549/100000000000000 : ℝ)^3273
        have hw : |(-1998189173/10000000000 : ℝ)|=(1998189173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010628177/2000000000 : ℝ)|^4297 ≤ (4081471737249/10000000000000 : ℝ)^3273
        have hw : |(1010628177/2000000000 : ℝ)|=(1010628177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5636700163/10000000000 : ℝ)|^4297 ≤ (2355591060151/5000000000000 : ℝ)^3273
        have hw : |(5636700163/10000000000 : ℝ)|=(5636700163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s1_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250929101/10000000000 : ℝ)*x 0 + (-431550719/2500000000 : ℝ)*x 1 + (140917487/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250929101/10000000000 : ℝ)^4297 ≤ (1716992669151/4000000000000 : ℝ)^3273 := by
    have hnat : (5250929101 : ℕ)^4297*4000000000000^3273 ≤ 1716992669151^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250929101 10000000000 1716992669151 4000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431550719/2500000000 : ℝ)^4297 ≤ (9963369539239/100000000000000 : ℝ)^3273 := by
    have hnat : (431550719 : ℕ)^4297*100000000000000^3273 ≤ 9963369539239^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431550719 2500000000 9963369539239 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140917487/250000000 : ℝ)^4297 ≤ (147224417839/312500000000 : ℝ)^3273 := by
    have hnat : (140917487 : ℕ)^4297*312500000000^3273 ≤ 147224417839^3273*250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140917487 250000000 147224417839 312500000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250929101/10000000000 : ℝ), (-431550719/2500000000 : ℝ), (140917487/250000000 : ℝ)] ![(1716992669151/4000000000000 : ℝ), (9963369539239/100000000000000 : ℝ), (147224417839/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250929101/10000000000 : ℝ)|^4297 ≤ (1716992669151/4000000000000 : ℝ)^3273
        have hw : |(5250929101/10000000000 : ℝ)|=(5250929101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431550719/2500000000 : ℝ)|^4297 ≤ (9963369539239/100000000000000 : ℝ)^3273
        have hw : |(-431550719/2500000000 : ℝ)|=(431550719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140917487/250000000 : ℝ)|^4297 ≤ (147224417839/312500000000 : ℝ)^3273
        have hw : |(140917487/250000000 : ℝ)|=(140917487/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s1_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250928519/10000000000 : ℝ)*x 0 + (563669929/1000000000 : ℝ)*x 1 + (-1726203977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250928519/10000000000 : ℝ)^4297 ≤ (21462405241297/50000000000000 : ℝ)^3273 := by
    have hnat : (5250928519 : ℕ)^4297*50000000000000^3273 ≤ 21462405241297^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250928519 10000000000 21462405241297 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563669929/1000000000 : ℝ)^4297 ≤ (9422362324723/20000000000000 : ℝ)^3273 := by
    have hnat : (563669929 : ℕ)^4297*20000000000000^3273 ≤ 9422362324723^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563669929 1000000000 9422362324723 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1726203977/10000000000 : ℝ)^4297 ≤ (9963377882217/100000000000000 : ℝ)^3273 := by
    have hnat : (1726203977 : ℕ)^4297*100000000000000^3273 ≤ 9963377882217^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726203977 10000000000 9963377882217 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250928519/10000000000 : ℝ), (563669929/1000000000 : ℝ), (-1726203977/10000000000 : ℝ)] ![(21462405241297/50000000000000 : ℝ), (9422362324723/20000000000000 : ℝ), (9963377882217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250928519/10000000000 : ℝ)|^4297 ≤ (21462405241297/50000000000000 : ℝ)^3273
        have hw : |(5250928519/10000000000 : ℝ)|=(5250928519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563669929/1000000000 : ℝ)|^4297 ≤ (9422362324723/20000000000000 : ℝ)^3273
        have hw : |(563669929/1000000000 : ℝ)|=(563669929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1726203977/10000000000 : ℝ)|^4297 ≤ (9963377882217/100000000000000 : ℝ)^3273
        have hw : |(-1726203977/10000000000 : ℝ)|=(1726203977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s1_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268396211/625000000 : ℝ)*x 0 + (4945722347/10000000000 : ℝ)*x 1 + (1862858393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268396211/625000000 : ℝ)^4297 ≤ (6592851306719/20000000000000 : ℝ)^3273 := by
    have hnat : (268396211 : ℕ)^4297*20000000000000^3273 ≤ 6592851306719^3273*625000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268396211 625000000 6592851306719 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4945722347/10000000000 : ℝ)^4297 ≤ (39679444526033/100000000000000 : ℝ)^3273 := by
    have hnat : (4945722347 : ℕ)^4297*100000000000000^3273 ≤ 39679444526033^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4945722347 10000000000 39679444526033 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1862858393/5000000000 : ℝ)^4297 ≤ (13678149462661/50000000000000 : ℝ)^3273 := by
    have hnat : (1862858393 : ℕ)^4297*50000000000000^3273 ≤ 13678149462661^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862858393 5000000000 13678149462661 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268396211/625000000 : ℝ), (4945722347/10000000000 : ℝ), (1862858393/5000000000 : ℝ)] ![(6592851306719/20000000000000 : ℝ), (39679444526033/100000000000000 : ℝ), (13678149462661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268396211/625000000 : ℝ)|^4297 ≤ (6592851306719/20000000000000 : ℝ)^3273
        have hw : |(268396211/625000000 : ℝ)|=(268396211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4945722347/10000000000 : ℝ)|^4297 ≤ (39679444526033/100000000000000 : ℝ)^3273
        have hw : |(4945722347/10000000000 : ℝ)|=(4945722347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1862858393/5000000000 : ℝ)|^4297 ≤ (13678149462661/50000000000000 : ℝ)^3273
        have hw : |(1862858393/5000000000 : ℝ)|=(1862858393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6843/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19499/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1377/100000 : ℝ) ^ (537/128 : ℝ) ≤ (311369659609/20000000000000000000 : ℝ) := by
    have hpowers : (1377/100000 : ℝ)^537 ≤ (311369659609/20000000000000000000 : ℝ)^128 := by
      have hnat : (1377 : ℕ)^537*20000000000000000000^128 ≤ 311369659609^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1377 100000 311369659609 20000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1377/100000 : ℝ)) (X := (311369659609/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (26907/100000 : ℝ) ^ (537/128 : ℝ) ≤ (50701019260811241/12500000000000000000 : ℝ) := by
    have hpowers : (26907/100000 : ℝ)^537 ≤ (50701019260811241/12500000000000000000 : ℝ)^128 := by
      have hnat : (26907 : ℕ)^537*12500000000000000000^128 ≤ 50701019260811241^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26907 100000 50701019260811241 12500000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26907/100000 : ℝ)) (X := (50701019260811241/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000311369659609/10000000000000000000 : ℝ) ≤ (5000000037109233/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (10000000311369659609/10000000000000000000 : ℝ)^128 ≤ (5000000037109233/5000000000000000 : ℝ)^537 := by
      have hnat : (10000000311369659609 : ℕ)^128*5000000000000000^537 ≤ 5000000037109233^537*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000311369659609 10000000000000000000 5000000037109233 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000037109233/5000000000000000 : ℝ)) (X := (10000000311369659609/10000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100405609710934787973/100000000000000000000 : ℝ) ≤ (2001930653213047/2000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (100405609710934787973/100000000000000000000 : ℝ)^128 ≤ (2001930653213047/2000000000000000 : ℝ)^537 := by
      have hnat : (100405609710934787973 : ℕ)^128*2000000000000000^537 ≤ 2001930653213047^537*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100405609710934787973 100000000000000000000 2001930653213047 2000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001930653213047/2000000000000000 : ℝ)) (X := (100405609710934787973/100000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (6300701019260811241/6250000000000000000 : ℝ) ≤ (2504826614478001/2500000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (6300701019260811241/6250000000000000000 : ℝ)^128 ≤ (2504826614478001/2500000000000000 : ℝ)^537 := by
      have hnat : (6300701019260811241 : ℕ)^128*2500000000000000^537 ≤ 2504826614478001^537*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6300701019260811241 6250000000000000000 2504826614478001 2500000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504826614478001/2500000000000000 : ℝ)) (X := (6300701019260811241/6250000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(311369659609/20000000000000000000 : ℝ) ≤ ((42545569500741905859/42550000000000000000 : ℝ)+2*(9653191846769/2553000000000000 : ℝ)*(1377/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (42545569500741905859/42550000000000000000 : ℝ)+2*(9653191846769/2553000000000000 : ℝ)*(1377/100000 : ℝ)=(5000000037109233/5000000000000000 : ℝ) by norm_num, show 1+2*(311369659609/20000000000000000000 : ℝ)=(10000000311369659609/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50701019260811241/12500000000000000000 : ℝ)+(311369659609/20000000000000000000 : ℝ) ≤ ((42545569500741905859/42550000000000000000 : ℝ)+(9653191846769/2553000000000000 : ℝ)*((26907/100000 : ℝ)+(1377/100000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (42545569500741905859/42550000000000000000 : ℝ)+(9653191846769/2553000000000000 : ℝ)*((26907/100000 : ℝ)+(1377/100000 : ℝ))=(2001930653213047/2000000000000000 : ℝ) by norm_num, show 1+(50701019260811241/12500000000000000000 : ℝ)+(311369659609/20000000000000000000 : ℝ)=(100405609710934787973/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50701019260811241/12500000000000000000 : ℝ) ≤ ((42545569500741905859/42550000000000000000 : ℝ)+2*(9653191846769/2553000000000000 : ℝ)*(26907/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (42545569500741905859/42550000000000000000 : ℝ)+2*(9653191846769/2553000000000000 : ℝ)*(26907/100000 : ℝ)=(2504826614478001/2500000000000000 : ℝ) by norm_num, show 1+2*(50701019260811241/12500000000000000000 : ℝ)=(6300701019260811241/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42545569500741905859/42550000000000000000 : ℝ)*(X 1 0+X 2 0)+(9653191846769/2553000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (1377/100000 : ℝ)) (hi := (26907/100000 : ℝ)) (c := (42545569500741905859/42550000000000000000 : ℝ)) (alpha := (9653191846769/2553000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42545569500741905859/42550000000000000000 : ℝ)*(X 0 1+X 2 1)+(9653191846769/2553000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (1377/100000 : ℝ)) (hi := (26907/100000 : ℝ)) (c := (42545569500741905859/42550000000000000000 : ℝ)) (alpha := (9653191846769/2553000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42545569500741905859/42550000000000000000 : ℝ)*(X 0 2+X 1 2)+(9653191846769/2553000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (1377/100000 : ℝ)) (hi := (26907/100000 : ℝ)) (c := (42545569500741905859/42550000000000000000 : ℝ)) (alpha := (9653191846769/2553000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1997643429/10000000000 : ℝ)*X 0 0+(1411094751/2500000000 : ℝ)*X 0 1+(2522799863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2703119441/5000000000 : ℝ)*X 1 0+(-2317303063/10000000000 : ℝ)*X 1 1+(504559957/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5406238923/10000000000 : ℝ)*X 2 0+(5045599347/10000000000 : ℝ)*X 2 1+(-1158651647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107329983/250000000 : ℝ)*X 0 0+(3709661153/10000000000 : ℝ)*X 0 1+(4961489277/10000000000 : ℝ)*X 0 2+(107329983/250000000 : ℝ)*X 1 0+(3709661153/10000000000 : ℝ)*X 1 1+(4961489277/10000000000 : ℝ)*X 1 2+(107329983/250000000 : ℝ)*X 2 0+(3709661153/10000000000 : ℝ)*X 2 1+(4961489277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1998189173/10000000000 : ℝ)*X 0 0+(1010628177/2000000000 : ℝ)*X 0 1+(5636700163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250929101/10000000000 : ℝ)*X 1 0+(-431550719/2500000000 : ℝ)*X 1 1+(140917487/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5250928519/10000000000 : ℝ)*X 2 0+(563669929/1000000000 : ℝ)*X 2 1+(-1726203977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((268396211/625000000 : ℝ)*X 0 0+(4945722347/10000000000 : ℝ)*X 0 1+(1862858393/5000000000 : ℝ)*X 0 2+(268396211/625000000 : ℝ)*X 1 0+(4945722347/10000000000 : ℝ)*X 1 1+(1862858393/5000000000 : ℝ)*X 1 2+(268396211/625000000 : ℝ)*X 2 0+(4945722347/10000000000 : ℝ)*X 2 1+(1862858393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (598081667250789161548909263/66484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22185379/20000000000000 : ℝ)*(base1) + (1485700359/100000000000000 : ℝ)*(base19) + (374591487/25000000000000 : ℝ)*(base23) + (237580077/100000000000000 : ℝ)*(upper3) + (146447559/100000000000000 : ℝ)*(upper5) + (38576857394527/3125000000000 : ℝ)*(major0) + (38576857394527/3125000000000 : ℝ)*(major1) + (38576857394527/3125000000000 : ℝ)*(major2) + (334014469099239/20000000000000 : ℝ)*(sp0) + (835038897294877/50000000000000 : ℝ)*(sp1) + (835038890962083/50000000000000 : ℝ)*(sp2) + (79883517313069/10000000000000 : ℝ)*(sp3) + (7045720813/100000000000000 : ℝ)*(sp4) + (1002260313/25000000000000 : ℝ)*(sp7) + (798839293098839/100000000000000 : ℝ)*(f.failure) + (835039640145057/50000000000000 : ℝ)*(f.sum) + (3142611331697/997265625000000000000000000 : ℝ)*base65 + (4112759343401432329/398906250000000000000000000000000 : ℝ)*base67 + (2611384325186432329/398906250000000000000000000000000 : ℝ)*base69 + (954773624590026079/398906250000000000000000000000000 : ℝ)*base71 + (60832881659851/7978125000000000000000000000 : ℝ)*base73 + (3731046079229713579/398906250000000000000000000000000 : ℝ)*base75 + (3049072049735338579/398906250000000000000000000000000 : ℝ)*base77 + (567483909135651079/398906250000000000000000000000000 : ℝ)*base79 + (135028898264929/31912500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6530557/10000000000000000000000 : ℝ)*base90 + (6530557/10000000000000000000000 : ℝ)*base92 + (6530557/10000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8428158624473770662267834933/1063750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (287705713/25000000000000 : ℝ)*(base19) + (850444061/100000000000000 : ℝ)*(base23) + (10464051/100000000000000 : ℝ)*(upper2) + (28242697/50000000000000 : ℝ)*(upper3) + (10631803/5000000000000 : ℝ)*(upper5) + (633322632227629/50000000000000 : ℝ)*(major0) + (633322632227629/50000000000000 : ℝ)*(major1) + (633322632227629/50000000000000 : ℝ)*(major2) + (2779671803/50000000000000 : ℝ)*(sp1) + (575751087/50000000000000 : ℝ)*(sp2) + (5355071830119/312500000000 : ℝ)*(sp4) + (856808137735811/50000000000000 : ℝ)*(sp5) + (342724196738369/20000000000000 : ℝ)*(sp6) + (409833639585161/50000000000000 : ℝ)*(sp7) + (409833639585161/50000000000000 : ℝ)*(f.failure) + (5355071830119/312500000000 : ℝ)*(f.sum) + (33945371701699/63825000000000000000000000000 : ℝ)*base66 + (16816416803689615067/6382500000000000000000000000000000 : ℝ)*base68 + (14793261667075384933/6382500000000000000000000000000000 : ℝ)*base69 + (46533163531579615067/6382500000000000000000000000000000 : ℝ)*base72 + (86949106149401/63825000000000000000000000000 : ℝ)*base73 + (12032379067474615067/6382500000000000000000000000000000 : ℝ)*base76 + (3241491325472884933/6382500000000000000000000000000000 : ℝ)*base77 + (27238207204399615067/6382500000000000000000000000000000 : ℝ)*base80 + (28792866400813/31912500000000000000000000000 : ℝ)*base81 + (30238557/5000000000000000000000 : ℝ)*base89 + (30238557/5000000000000000000000 : ℝ)*base91 + (30238557/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1337_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19499/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1337_s2_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-509558803/2500000000 : ℝ)*x 0 + (171285149/312500000 : ℝ)*x 1 + (1295714949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509558803/2500000000 : ℝ)^4297 ≤ (12392121263403/100000000000000 : ℝ)^3273 := by
    have hnat : (509558803 : ℕ)^4297*100000000000000^3273 ≤ 12392121263403^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509558803 2500000000 12392121263403 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171285149/312500000 : ℝ)^4297 ≤ (5676514298817/12500000000000 : ℝ)^3273 := by
    have hnat : (171285149 : ℕ)^4297*12500000000000^3273 ≤ 5676514298817^3273*312500000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171285149 312500000 5676514298817 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295714949/2500000000 : ℝ)^4297 ≤ (42195764334839/100000000000000 : ℝ)^3273 := by
    have hnat : (1295714949 : ℕ)^4297*100000000000000^3273 ≤ 42195764334839^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295714949 2500000000 42195764334839 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509558803/2500000000 : ℝ), (171285149/312500000 : ℝ), (1295714949/2500000000 : ℝ)] ![(12392121263403/100000000000000 : ℝ), (5676514298817/12500000000000 : ℝ), (42195764334839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509558803/2500000000 : ℝ)|^4297 ≤ (12392121263403/100000000000000 : ℝ)^3273
        have hw : |(-509558803/2500000000 : ℝ)|=(509558803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171285149/312500000 : ℝ)|^4297 ≤ (5676514298817/12500000000000 : ℝ)^3273
        have hw : |(171285149/312500000 : ℝ)|=(171285149/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295714949/2500000000 : ℝ)|^4297 ≤ (42195764334839/100000000000000 : ℝ)^3273
        have hw : |(1295714949/2500000000 : ℝ)|=(1295714949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s2_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5366306121/10000000000 : ℝ)*x 0 + (-548098333/2500000000 : ℝ)*x 1 + (5182860179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366306121/10000000000 : ℝ)^4297 ≤ (22083654574583/50000000000000 : ℝ)^3273 := by
    have hnat : (5366306121 : ℕ)^4297*50000000000000^3273 ≤ 22083654574583^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366306121 10000000000 22083654574583 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548098333/2500000000 : ℝ)^4297 ≤ (6818461200553/50000000000000 : ℝ)^3273 := by
    have hnat : (548098333 : ℕ)^4297*50000000000000^3273 ≤ 6818461200553^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548098333 2500000000 6818461200553 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182860179/10000000000 : ℝ)^4297 ≤ (42195768428553/100000000000000 : ℝ)^3273 := by
    have hnat : (5182860179 : ℕ)^4297*100000000000000^3273 ≤ 42195768428553^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182860179 10000000000 42195768428553 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366306121/10000000000 : ℝ), (-548098333/2500000000 : ℝ), (5182860179/10000000000 : ℝ)] ![(22083654574583/50000000000000 : ℝ), (6818461200553/50000000000000 : ℝ), (42195768428553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366306121/10000000000 : ℝ)|^4297 ≤ (22083654574583/50000000000000 : ℝ)^3273
        have hw : |(5366306121/10000000000 : ℝ)|=(5366306121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548098333/2500000000 : ℝ)|^4297 ≤ (6818461200553/50000000000000 : ℝ)^3273
        have hw : |(-548098333/2500000000 : ℝ)|=(548098333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182860179/10000000000 : ℝ)|^4297 ≤ (42195768428553/100000000000000 : ℝ)^3273
        have hw : |(5182860179/10000000000 : ℝ)|=(5182860179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s2_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536630621/1000000000 : ℝ)*x 0 + (207314403/400000000 : ℝ)*x 1 + (-2192393351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536630621/1000000000 : ℝ)^4297 ≤ (8833462022171/20000000000000 : ℝ)^3273 := by
    have hnat : (536630621 : ℕ)^4297*20000000000000^3273 ≤ 8833462022171^3273*1000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536630621 1000000000 8833462022171 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207314403/400000000 : ℝ)^4297 ≤ (2637235457309/6250000000000 : ℝ)^3273 := by
    have hnat : (207314403 : ℕ)^4297*6250000000000^3273 ≤ 2637235457309^3273*400000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207314403 400000000 2637235457309 6250000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192393351/10000000000 : ℝ)^4297 ≤ (13636922556263/100000000000000 : ℝ)^3273 := by
    have hnat : (2192393351 : ℕ)^4297*100000000000000^3273 ≤ 13636922556263^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192393351 10000000000 13636922556263 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536630621/1000000000 : ℝ), (207314403/400000000 : ℝ), (-2192393351/10000000000 : ℝ)] ![(8833462022171/20000000000000 : ℝ), (2637235457309/6250000000000 : ℝ), (13636922556263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536630621/1000000000 : ℝ)|^4297 ≤ (8833462022171/20000000000000 : ℝ)^3273
        have hw : |(536630621/1000000000 : ℝ)|=(536630621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207314403/400000000 : ℝ)|^4297 ≤ (2637235457309/6250000000000 : ℝ)^3273
        have hw : |(207314403/400000000 : ℝ)|=(207314403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192393351/10000000000 : ℝ)|^4297 ≤ (13636922556263/100000000000000 : ℝ)^3273
        have hw : |(-2192393351/10000000000 : ℝ)|=(2192393351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s2_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (864313177/2000000000 : ℝ)*x 0 + (251268281/625000000 : ℝ)*x 1 + (4643854291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864313177/2000000000 : ℝ)^4297 ≤ (33238911920831/100000000000000 : ℝ)^3273 := by
    have hnat : (864313177 : ℕ)^4297*100000000000000^3273 ≤ 33238911920831^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864313177 2000000000 33238911920831 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251268281/625000000 : ℝ)^4297 ≤ (30230448140453/100000000000000 : ℝ)^3273 := by
    have hnat : (251268281 : ℕ)^4297*100000000000000^3273 ≤ 30230448140453^3273*625000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251268281 625000000 30230448140453 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4643854291/10000000000 : ℝ)^4297 ≤ (36530639930789/100000000000000 : ℝ)^3273 := by
    have hnat : (4643854291 : ℕ)^4297*100000000000000^3273 ≤ 36530639930789^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643854291 10000000000 36530639930789 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864313177/2000000000 : ℝ), (251268281/625000000 : ℝ), (4643854291/10000000000 : ℝ)] ![(33238911920831/100000000000000 : ℝ), (30230448140453/100000000000000 : ℝ), (36530639930789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864313177/2000000000 : ℝ)|^4297 ≤ (33238911920831/100000000000000 : ℝ)^3273
        have hw : |(864313177/2000000000 : ℝ)|=(864313177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251268281/625000000 : ℝ)|^4297 ≤ (30230448140453/100000000000000 : ℝ)^3273
        have hw : |(251268281/625000000 : ℝ)|=(251268281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4643854291/10000000000 : ℝ)|^4297 ≤ (36530639930789/100000000000000 : ℝ)^3273
        have hw : |(4643854291/10000000000 : ℝ)|=(4643854291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s2_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019151333/5000000000 : ℝ)*x 0 + (1036948279/2000000000 : ℝ)*x 1 + (5479226113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019151333/5000000000 : ℝ)^4297 ≤ (12392659682753/100000000000000 : ℝ)^3273 := by
    have hnat : (1019151333 : ℕ)^4297*100000000000000^3273 ≤ 12392659682753^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019151333 5000000000 12392659682753 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036948279/2000000000 : ℝ)^4297 ≤ (42215877039703/100000000000000 : ℝ)^3273 := by
    have hnat : (1036948279 : ℕ)^4297*100000000000000^3273 ≤ 42215877039703^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036948279 2000000000 42215877039703 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479226113/10000000000 : ℝ)^4297 ≤ (45391463256533/100000000000000 : ℝ)^3273 := by
    have hnat : (5479226113 : ℕ)^4297*100000000000000^3273 ≤ 45391463256533^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479226113 10000000000 45391463256533 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019151333/5000000000 : ℝ), (1036948279/2000000000 : ℝ), (5479226113/10000000000 : ℝ)] ![(12392659682753/100000000000000 : ℝ), (42215877039703/100000000000000 : ℝ), (45391463256533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019151333/5000000000 : ℝ)|^4297 ≤ (12392659682753/100000000000000 : ℝ)^3273
        have hw : |(-1019151333/5000000000 : ℝ)|=(1019151333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036948279/2000000000 : ℝ)|^4297 ≤ (42215877039703/100000000000000 : ℝ)^3273
        have hw : |(1036948279/2000000000 : ℝ)|=(1036948279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479226113/10000000000 : ℝ)|^4297 ≤ (45391463256533/100000000000000 : ℝ)^3273
        have hw : |(5479226113/10000000000 : ℝ)|=(5479226113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s2_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289470253/10000000000 : ℝ)*x 0 + (-1896027101/10000000000 : ℝ)*x 1 + (5479226127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289470253/10000000000 : ℝ)^4297 ≤ (8667784992463/20000000000000 : ℝ)^3273 := by
    have hnat : (5289470253 : ℕ)^4297*20000000000000^3273 ≤ 8667784992463^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289470253 10000000000 8667784992463 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896027101/10000000000 : ℝ)^4297 ≤ (44021920387/390625000000 : ℝ)^3273 := by
    have hnat : (1896027101 : ℕ)^4297*390625000000^3273 ≤ 44021920387^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896027101 10000000000 44021920387 390625000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479226127/10000000000 : ℝ)^4297 ≤ (22695731704399/50000000000000 : ℝ)^3273 := by
    have hnat : (5479226127 : ℕ)^4297*50000000000000^3273 ≤ 22695731704399^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479226127 10000000000 22695731704399 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289470253/10000000000 : ℝ), (-1896027101/10000000000 : ℝ), (5479226127/10000000000 : ℝ)] ![(8667784992463/20000000000000 : ℝ), (44021920387/390625000000 : ℝ), (22695731704399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289470253/10000000000 : ℝ)|^4297 ≤ (8667784992463/20000000000000 : ℝ)^3273
        have hw : |(5289470253/10000000000 : ℝ)|=(5289470253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1896027101/10000000000 : ℝ)|^4297 ≤ (44021920387/390625000000 : ℝ)^3273
        have hw : |(-1896027101/10000000000 : ℝ)|=(1896027101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479226127/10000000000 : ℝ)|^4297 ≤ (22695731704399/50000000000000 : ℝ)^3273
        have hw : |(5479226127/10000000000 : ℝ)|=(5479226127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s2_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057894057/2000000000 : ℝ)*x 0 + (136980653/250000000 : ℝ)*x 1 + (-948013533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057894057/2000000000 : ℝ)^4297 ≤ (8667785061307/20000000000000 : ℝ)^3273 := by
    have hnat : (1057894057 : ℕ)^4297*20000000000000^3273 ≤ 8667785061307^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057894057 2000000000 8667785061307 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136980653/250000000 : ℝ)^4297 ≤ (22695731666333/50000000000000 : ℝ)^3273 := by
    have hnat : (136980653 : ℕ)^4297*50000000000000^3273 ≤ 22695731666333^3273*250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136980653 250000000 22695731666333 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948013533/5000000000 : ℝ)^4297 ≤ (11269611345953/100000000000000 : ℝ)^3273 := by
    have hnat : (948013533 : ℕ)^4297*100000000000000^3273 ≤ 11269611345953^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948013533 5000000000 11269611345953 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057894057/2000000000 : ℝ), (136980653/250000000 : ℝ), (-948013533/5000000000 : ℝ)] ![(8667785061307/20000000000000 : ℝ), (22695731666333/50000000000000 : ℝ), (11269611345953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057894057/2000000000 : ℝ)|^4297 ≤ (8667785061307/20000000000000 : ℝ)^3273
        have hw : |(1057894057/2000000000 : ℝ)|=(1057894057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136980653/250000000 : ℝ)|^4297 ≤ (22695731666333/50000000000000 : ℝ)^3273
        have hw : |(136980653/250000000 : ℝ)|=(136980653/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948013533/5000000000 : ℝ)|^4297 ≤ (11269611345953/100000000000000 : ℝ)^3273
        have hw : |(-948013533/5000000000 : ℝ)|=(948013533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s2_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160853637/5000000000 : ℝ)*x 0 + (4639921229/10000000000 : ℝ)*x 1 + (4024261267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160853637/5000000000 : ℝ)^4297 ≤ (33240339640209/100000000000000 : ℝ)^3273 := by
    have hnat : (2160853637 : ℕ)^4297*100000000000000^3273 ≤ 33240339640209^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160853637 5000000000 33240339640209 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4639921229/10000000000 : ℝ)^4297 ≤ (36490026349901/100000000000000 : ℝ)^3273 := by
    have hnat : (4639921229 : ℕ)^4297*100000000000000^3273 ≤ 36490026349901^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4639921229 10000000000 36490026349901 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024261267/10000000000 : ℝ)^4297 ≤ (30269633999259/100000000000000 : ℝ)^3273 := by
    have hnat : (4024261267 : ℕ)^4297*100000000000000^3273 ≤ 30269633999259^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024261267 10000000000 30269633999259 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160853637/5000000000 : ℝ), (4639921229/10000000000 : ℝ), (4024261267/10000000000 : ℝ)] ![(33240339640209/100000000000000 : ℝ), (36490026349901/100000000000000 : ℝ), (30269633999259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160853637/5000000000 : ℝ)|^4297 ≤ (33240339640209/100000000000000 : ℝ)^3273
        have hw : |(2160853637/5000000000 : ℝ)|=(2160853637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4639921229/10000000000 : ℝ)|^4297 ≤ (36490026349901/100000000000000 : ℝ)^3273
        have hw : |(4639921229/10000000000 : ℝ)|=(4639921229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024261267/10000000000 : ℝ)|^4297 ≤ (30269633999259/100000000000000 : ℝ)^3273
        have hw : |(4024261267/10000000000 : ℝ)|=(4024261267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19499/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9819/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4031/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19499/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19499/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19499/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19499/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19499/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19499/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6843/100000 : ℝ) ^ (537/128 : ℝ) ≤ (259731871887597/20000000000000000000 : ℝ) := by
    have hpowers : (6843/100000 : ℝ)^537 ≤ (259731871887597/20000000000000000000 : ℝ)^128 := by
      have hnat : (6843 : ℕ)^537*20000000000000000000^128 ≤ 259731871887597^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6843 100000 259731871887597 20000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6843/100000 : ℝ)) (X := (259731871887597/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (19499/100000 : ℝ) ^ (537/128 : ℝ) ≤ (2626152251780299/2500000000000000000 : ℝ) := by
    have hpowers : (19499/100000 : ℝ)^537 ≤ (2626152251780299/2500000000000000000 : ℝ)^128 := by
      have hnat : (19499 : ℕ)^537*2500000000000000000^128 ≤ 2626152251780299^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19499 100000 2626152251780299 2500000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19499/100000 : ℝ)) (X := (2626152251780299/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000259731871887597/10000000000000000000 : ℝ) ≤ (2500015477351383/2500000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (10000259731871887597/10000000000000000000 : ℝ)^128 ≤ (2500015477351383/2500000000000000 : ℝ)^537 := by
      have hnat : (10000259731871887597 : ℕ)^128*2500000000000000^537 ≤ 2500015477351383^537*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000259731871887597 10000000000000000000 2500015477351383 2500000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500015477351383/2500000000000000 : ℝ)) (X := (10000259731871887597/10000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20021268949886129989/20000000000000000000 : ℝ) ≤ (10002533820988537/10000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (20021268949886129989/20000000000000000000 : ℝ)^128 ≤ (10002533820988537/10000000000000000 : ℝ)^537 := by
      have hnat : (20021268949886129989 : ℕ)^128*10000000000000000^537 ≤ 10002533820988537^537*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20021268949886129989 20000000000000000000 10002533820988537 10000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002533820988537/10000000000000000 : ℝ)) (X := (20021268949886129989/20000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (1252626152251780299/1250000000000000000 : ℝ) ≤ (5002502866285771/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (1252626152251780299/1250000000000000000 : ℝ)^128 ≤ (5002502866285771/5000000000000000 : ℝ)^537 := by
      have hnat : (1252626152251780299 : ℕ)^128*5000000000000000^537 ≤ 5002502866285771^537*1250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1252626152251780299 1250000000000000000 5002502866285771 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002502866285771/5000000000000000 : ℝ)) (X := (1252626152251780299/1250000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(259731871887597/20000000000000000000 : ℝ) ≤ ((63263476471755703281/63280000000000000000 : ℝ)+2*(494382316601/253120000000000 : ℝ)*(6843/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (63263476471755703281/63280000000000000000 : ℝ)+2*(494382316601/253120000000000 : ℝ)*(6843/100000 : ℝ)=(2500015477351383/2500000000000000 : ℝ) by norm_num, show 1+2*(259731871887597/20000000000000000000 : ℝ)=(10000259731871887597/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2626152251780299/2500000000000000000 : ℝ)+(259731871887597/20000000000000000000 : ℝ) ≤ ((63263476471755703281/63280000000000000000 : ℝ)+(494382316601/253120000000000 : ℝ)*((19499/100000 : ℝ)+(6843/100000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (63263476471755703281/63280000000000000000 : ℝ)+(494382316601/253120000000000 : ℝ)*((19499/100000 : ℝ)+(6843/100000 : ℝ))=(10002533820988537/10000000000000000 : ℝ) by norm_num, show 1+(2626152251780299/2500000000000000000 : ℝ)+(259731871887597/20000000000000000000 : ℝ)=(20021268949886129989/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2626152251780299/2500000000000000000 : ℝ) ≤ ((63263476471755703281/63280000000000000000 : ℝ)+2*(494382316601/253120000000000 : ℝ)*(19499/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (63263476471755703281/63280000000000000000 : ℝ)+2*(494382316601/253120000000000 : ℝ)*(19499/100000 : ℝ)=(5002502866285771/5000000000000000 : ℝ) by norm_num, show 1+2*(2626152251780299/2500000000000000000 : ℝ)=(1252626152251780299/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63263476471755703281/63280000000000000000 : ℝ)*(X 1 0+X 2 0)+(494382316601/253120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (6843/100000 : ℝ)) (hi := (19499/100000 : ℝ)) (c := (63263476471755703281/63280000000000000000 : ℝ)) (alpha := (494382316601/253120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63263476471755703281/63280000000000000000 : ℝ)*(X 0 1+X 2 1)+(494382316601/253120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (6843/100000 : ℝ)) (hi := (19499/100000 : ℝ)) (c := (63263476471755703281/63280000000000000000 : ℝ)) (alpha := (494382316601/253120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63263476471755703281/63280000000000000000 : ℝ)*(X 0 2+X 1 2)+(494382316601/253120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (6843/100000 : ℝ)) (hi := (19499/100000 : ℝ)) (c := (63263476471755703281/63280000000000000000 : ℝ)) (alpha := (494382316601/253120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-509558803/2500000000 : ℝ)*X 0 0+(171285149/312500000 : ℝ)*X 0 1+(1295714949/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5366306121/10000000000 : ℝ)*X 1 0+(-548098333/2500000000 : ℝ)*X 1 1+(5182860179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536630621/1000000000 : ℝ)*X 2 0+(207314403/400000000 : ℝ)*X 2 1+(-2192393351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((864313177/2000000000 : ℝ)*X 0 0+(251268281/625000000 : ℝ)*X 0 1+(4643854291/10000000000 : ℝ)*X 0 2+(864313177/2000000000 : ℝ)*X 1 0+(251268281/625000000 : ℝ)*X 1 1+(4643854291/10000000000 : ℝ)*X 1 2+(864313177/2000000000 : ℝ)*X 2 0+(251268281/625000000 : ℝ)*X 2 1+(4643854291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1019151333/5000000000 : ℝ)*X 0 0+(1036948279/2000000000 : ℝ)*X 0 1+(5479226113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289470253/10000000000 : ℝ)*X 1 0+(-1896027101/10000000000 : ℝ)*X 1 1+(5479226127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057894057/2000000000 : ℝ)*X 2 0+(136980653/250000000 : ℝ)*X 2 1+(-948013533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160853637/5000000000 : ℝ)*X 0 0+(4639921229/10000000000 : ℝ)*X 0 1+(4024261267/10000000000 : ℝ)*X 0 2+(2160853637/5000000000 : ℝ)*X 1 0+(4639921229/10000000000 : ℝ)*X 1 1+(4024261267/10000000000 : ℝ)*X 1 2+(2160853637/5000000000 : ℝ)*X 2 0+(4639921229/10000000000 : ℝ)*X 2 1+(4024261267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14541502370288304367875992169/3164000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (747886831/100000000000000 : ℝ)*(base19) + (803352597/100000000000000 : ℝ)*(base23) + (99900117/100000000000000 : ℝ)*(upper3) + (74837/100000000000000 : ℝ)*(upper4) + (24246683/25000000000000 : ℝ)*(upper5) + (2478225257166483/100000000000000 : ℝ)*(major0) + (2478225257166483/100000000000000 : ℝ)*(major1) + (2478225257166483/100000000000000 : ℝ)*(major2) + (3352736340519901/100000000000000 : ℝ)*(sp0) + (3352748710781379/100000000000000 : ℝ)*(sp1) + (1676374327657807/50000000000000 : ℝ)*(sp2) + (1603695495509267/100000000000000 : ℝ)*(sp3) + (13118148309/100000000000000 : ℝ)*(sp4) + (5406958027/100000000000000 : ℝ)*(sp7) + (801850451233647/50000000000000 : ℝ)*(f.failure) + (335274945866821/10000000000000 : ℝ)*(f.sum) + (30717043829589/12656000000000000000000000000 : ℝ)*base66 + (61514537115226919277/6328000000000000000000000000000000 : ℝ)*base68 + (8110716929805080723/6328000000000000000000000000000000 : ℝ)*base69 + (55367460419018919277/6328000000000000000000000000000000 : ℝ)*base72 + (45073401475989/12656000000000000000000000000 : ℝ)*base74 + (40509925140978919277/6328000000000000000000000000000000 : ℝ)*base76 + (32606660492413080723/6328000000000000000000000000000000 : ℝ)*base77 + (109196979142082919277/6328000000000000000000000000000000 : ℝ)*base80 + (25083522908869/12656000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9609861/5000000000000000000000 : ℝ)*base90 + (9609861/5000000000000000000000 : ℝ)*base92 + (9609861/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1327772856197036892461256087/197750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1371761787/100000000000000 : ℝ)*(base19) + (1580997257/100000000000000 : ℝ)*(base23) + (8810159/5000000000000 : ℝ)*(upper3) + (1472319/2000000000000 : ℝ)*(lower4) + (24386611/25000000000000 : ℝ)*(upper5) + (156876047292497/6250000000000 : ℝ)*(major0) + (156876047292497/6250000000000 : ℝ)*(major1) + (156876047292497/6250000000000 : ℝ)*(major2) + (7569921101/50000000000000 : ℝ)*(sp1) + (9274333363/50000000000000 : ℝ)*(sp2) + (1697879788719649/50000000000000 : ℝ)*(sp4) + (3395743065835309/100000000000000 : ℝ)*(sp5) + (679147889555063/20000000000000 : ℝ)*(sp6) + (812136856053609/50000000000000 : ℝ)*(sp7) + (812136856053609/50000000000000 : ℝ)*(f.failure) + (1697879788719649/50000000000000 : ℝ)*(f.sum) + (4857145048873/791000000000000000000000000 : ℝ)*base65 + (4829858168367832657/395500000000000000000000000000000 : ℝ)*base67 + (2389131859283832657/395500000000000000000000000000000 : ℝ)*base69 + (3984629692503332657/395500000000000000000000000000000 : ℝ)*base71 + (2615766872669/395500000000000000000000000 : ℝ)*base73 + (4775023685255332657/395500000000000000000000000000000 : ℝ)*base75 + (75546603375332657/395500000000000000000000000000000 : ℝ)*base77 + (7177051184297832657/395500000000000000000000000000000 : ℝ)*base79 + (1461717966007/791000000000000000000000000 : ℝ)*base81 + (41472067/5000000000000000000000 : ℝ)*base90 + (41472067/5000000000000000000000 : ℝ)*base92 + (41472067/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1337_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19499/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9819/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4031/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1337_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9819/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4031/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1337_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1337_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1337_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9819/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4031/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1337_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
