-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1427_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:57.625208+00:00
-- url     : https://prove2.me/submissions/cc8da4c8-5d19-4879-9215-6e53037ed4fc

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
theorem support_rectangle_w1427_s0_0 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1759946687/10000000000 : ℝ)*x 0 + (372562917/625000000 : ℝ)*x 1 + (1207695129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759946687/10000000000 : ℝ)^4387 ≤ (5184795527697/50000000000000 : ℝ)^3363 := by
    have hnat : (1759946687 : ℕ)^4387*50000000000000^3363 ≤ 5184795527697^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759946687 10000000000 5184795527697 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (372562917/625000000 : ℝ)^4387 ≤ (12730535588907/25000000000000 : ℝ)^3363 := by
    have hnat : (372562917 : ℕ)^4387*25000000000000^3363 ≤ 12730535588907^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372562917 625000000 12730535588907 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207695129/2500000000 : ℝ)^4387 ≤ (19354133287593/50000000000000 : ℝ)^3363 := by
    have hnat : (1207695129 : ℕ)^4387*50000000000000^3363 ≤ 19354133287593^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207695129 2500000000 19354133287593 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1759946687/10000000000 : ℝ), (372562917/625000000 : ℝ), (1207695129/2500000000 : ℝ)] ![(5184795527697/50000000000000 : ℝ), (12730535588907/25000000000000 : ℝ), (19354133287593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1759946687/10000000000 : ℝ)|^4387 ≤ (5184795527697/50000000000000 : ℝ)^3363
        have hw : |(-1759946687/10000000000 : ℝ)|=(1759946687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(372562917/625000000 : ℝ)|^4387 ≤ (12730535588907/25000000000000 : ℝ)^3363
        have hw : |(372562917/625000000 : ℝ)|=(372562917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207695129/2500000000 : ℝ)|^4387 ≤ (19354133287593/50000000000000 : ℝ)^3363
        have hw : |(1207695129/2500000000 : ℝ)|=(1207695129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s0_1 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5492321629/10000000000 : ℝ)*x 0 + (-23984961/100000000 : ℝ)*x 1 + (4830780947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492321629/10000000000 : ℝ)^4387 ≤ (45762974413857/100000000000000 : ℝ)^3363 := by
    have hnat : (5492321629 : ℕ)^4387*100000000000000^3363 ≤ 45762974413857^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492321629 10000000000 45762974413857 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23984961/100000000 : ℝ)^4387 ≤ (7764377245609/50000000000000 : ℝ)^3363 := by
    have hnat : (23984961 : ℕ)^4387*50000000000000^3363 ≤ 7764377245609^3363*100000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23984961 100000000 7764377245609 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4830780947/10000000000 : ℝ)^4387 ≤ (19354135540143/50000000000000 : ℝ)^3363 := by
    have hnat : (4830780947 : ℕ)^4387*50000000000000^3363 ≤ 19354135540143^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830780947 10000000000 19354135540143 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492321629/10000000000 : ℝ), (-23984961/100000000 : ℝ), (4830780947/10000000000 : ℝ)] ![(45762974413857/100000000000000 : ℝ), (7764377245609/50000000000000 : ℝ), (19354135540143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492321629/10000000000 : ℝ)|^4387 ≤ (45762974413857/100000000000000 : ℝ)^3363
        have hw : |(5492321629/10000000000 : ℝ)|=(5492321629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23984961/100000000 : ℝ)|^4387 ≤ (7764377245609/50000000000000 : ℝ)^3363
        have hw : |(-23984961/100000000 : ℝ)|=(23984961/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4830780947/10000000000 : ℝ)|^4387 ≤ (19354135540143/50000000000000 : ℝ)^3363
        have hw : |(4830780947/10000000000 : ℝ)|=(4830780947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s0_2 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343270131/625000000 : ℝ)*x 0 + (2415390383/5000000000 : ℝ)*x 1 + (-1199247861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343270131/625000000 : ℝ)^4387 ≤ (45762979489791/100000000000000 : ℝ)^3363 := by
    have hnat : (343270131 : ℕ)^4387*100000000000000^3363 ≤ 45762979489791^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343270131 625000000 45762979489791 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2415390383/5000000000 : ℝ)^4387 ≤ (38708269188353/100000000000000 : ℝ)^3363 := by
    have hnat : (2415390383 : ℕ)^4387*100000000000000^3363 ≤ 38708269188353^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415390383 5000000000 38708269188353 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199247861/5000000000 : ℝ)^4387 ≤ (15528751298723/100000000000000 : ℝ)^3363 := by
    have hnat : (1199247861 : ℕ)^4387*100000000000000^3363 ≤ 15528751298723^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199247861 5000000000 15528751298723 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343270131/625000000 : ℝ), (2415390383/5000000000 : ℝ), (-1199247861/5000000000 : ℝ)] ![(45762979489791/100000000000000 : ℝ), (38708269188353/100000000000000 : ℝ), (15528751298723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343270131/625000000 : ℝ)|^4387 ≤ (45762979489791/100000000000000 : ℝ)^3363
        have hw : |(343270131/625000000 : ℝ)|=(343270131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2415390383/5000000000 : ℝ)|^4387 ≤ (38708269188353/100000000000000 : ℝ)^3363
        have hw : |(2415390383/5000000000 : ℝ)|=(2415390383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1199247861/5000000000 : ℝ)|^4387 ≤ (15528751298723/100000000000000 : ℝ)^3363
        have hw : |(-1199247861/5000000000 : ℝ)|=(1199247861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s0_3 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166287627/10000000000 : ℝ)*x 0 + (1551703399/5000000000 : ℝ)*x 1 + (5546673099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166287627/10000000000 : ℝ)^4387 ≤ (7978232563059/25000000000000 : ℝ)^3363 := by
    have hnat : (4166287627 : ℕ)^4387*25000000000000^3363 ≤ 7978232563059^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166287627 10000000000 7978232563059 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551703399/5000000000 : ℝ)^4387 ≤ (21732448313119/100000000000000 : ℝ)^3363 := by
    have hnat : (1551703399 : ℕ)^4387*100000000000000^3363 ≤ 21732448313119^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551703399 5000000000 21732448313119 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5546673099/10000000000 : ℝ)^4387 ≤ (46354621415693/100000000000000 : ℝ)^3363 := by
    have hnat : (5546673099 : ℕ)^4387*100000000000000^3363 ≤ 46354621415693^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5546673099 10000000000 46354621415693 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166287627/10000000000 : ℝ), (1551703399/5000000000 : ℝ), (5546673099/10000000000 : ℝ)] ![(7978232563059/25000000000000 : ℝ), (21732448313119/100000000000000 : ℝ), (46354621415693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166287627/10000000000 : ℝ)|^4387 ≤ (7978232563059/25000000000000 : ℝ)^3363
        have hw : |(4166287627/10000000000 : ℝ)|=(4166287627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551703399/5000000000 : ℝ)|^4387 ≤ (21732448313119/100000000000000 : ℝ)^3363
        have hw : |(1551703399/5000000000 : ℝ)|=(1551703399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5546673099/10000000000 : ℝ)|^4387 ≤ (46354621415693/100000000000000 : ℝ)^3363
        have hw : |(5546673099/10000000000 : ℝ)|=(5546673099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s0_4 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763973523/10000000000 : ℝ)*x 0 + (4859702849/10000000000 : ℝ)*x 1 + (5931051733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763973523/10000000000 : ℝ)^4387 ≤ (416022090841/4000000000000 : ℝ)^3363 := by
    have hnat : (1763973523 : ℕ)^4387*4000000000000^3363 ≤ 416022090841^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763973523 10000000000 416022090841 4000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4859702849/10000000000 : ℝ)^4387 ≤ (39010857319919/100000000000000 : ℝ)^3363 := by
    have hnat : (4859702849 : ℕ)^4387*100000000000000^3363 ≤ 39010857319919^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859702849 10000000000 39010857319919 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5931051733/10000000000 : ℝ)^4387 ≤ (25294295199963/50000000000000 : ℝ)^3363 := by
    have hnat : (5931051733 : ℕ)^4387*50000000000000^3363 ≤ 25294295199963^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931051733 10000000000 25294295199963 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763973523/10000000000 : ℝ), (4859702849/10000000000 : ℝ), (5931051733/10000000000 : ℝ)] ![(416022090841/4000000000000 : ℝ), (39010857319919/100000000000000 : ℝ), (25294295199963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763973523/10000000000 : ℝ)|^4387 ≤ (416022090841/4000000000000 : ℝ)^3363
        have hw : |(-1763973523/10000000000 : ℝ)|=(1763973523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4859702849/10000000000 : ℝ)|^4387 ≤ (39010857319919/100000000000000 : ℝ)^3363
        have hw : |(4859702849/10000000000 : ℝ)|=(4859702849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5931051733/10000000000 : ℝ)|^4387 ≤ (25294295199963/50000000000000 : ℝ)^3363
        have hw : |(5931051733/10000000000 : ℝ)|=(5931051733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s0_5 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207353893/400000000 : ℝ)*x 0 + (-259644933/2000000000 : ℝ)*x 1 + (5931051809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207353893/400000000 : ℝ)^4387 ≤ (42439146406023/100000000000000 : ℝ)^3363 := by
    have hnat : (207353893 : ℕ)^4387*100000000000000^3363 ≤ 42439146406023^3363*400000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207353893 400000000 42439146406023 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259644933/2000000000 : ℝ)^4387 ≤ (871532792147/12500000000000 : ℝ)^3363 := by
    have hnat : (259644933 : ℕ)^4387*12500000000000^3363 ≤ 871532792147^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259644933 2000000000 871532792147 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5931051809/10000000000 : ℝ)^4387 ≤ (25294295622773/50000000000000 : ℝ)^3363 := by
    have hnat : (5931051809 : ℕ)^4387*50000000000000^3363 ≤ 25294295622773^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931051809 10000000000 25294295622773 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207353893/400000000 : ℝ), (-259644933/2000000000 : ℝ), (5931051809/10000000000 : ℝ)] ![(42439146406023/100000000000000 : ℝ), (871532792147/12500000000000 : ℝ), (25294295622773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207353893/400000000 : ℝ)|^4387 ≤ (42439146406023/100000000000000 : ℝ)^3363
        have hw : |(207353893/400000000 : ℝ)|=(207353893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259644933/2000000000 : ℝ)|^4387 ≤ (871532792147/12500000000000 : ℝ)^3363
        have hw : |(-259644933/2000000000 : ℝ)|=(259644933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5931051809/10000000000 : ℝ)|^4387 ≤ (25294295622773/50000000000000 : ℝ)^3363
        have hw : |(5931051809/10000000000 : ℝ)|=(5931051809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s0_6 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036769469/2000000000 : ℝ)*x 0 + (1186210329/2000000000 : ℝ)*x 1 + (-649112447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036769469/2000000000 : ℝ)^4387 ≤ (8487829323923/20000000000000 : ℝ)^3363 := by
    have hnat : (1036769469 : ℕ)^4387*20000000000000^3363 ≤ 8487829323923^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036769469 2000000000 8487829323923 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1186210329/2000000000 : ℝ)^4387 ≤ (50588589420787/100000000000000 : ℝ)^3363 := by
    have hnat : (1186210329 : ℕ)^4387*100000000000000^3363 ≤ 50588589420787^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186210329 2000000000 50588589420787 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649112447/5000000000 : ℝ)^4387 ≤ (697226394153/10000000000000 : ℝ)^3363 := by
    have hnat : (649112447 : ℕ)^4387*10000000000000^3363 ≤ 697226394153^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649112447 5000000000 697226394153 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036769469/2000000000 : ℝ), (1186210329/2000000000 : ℝ), (-649112447/5000000000 : ℝ)] ![(8487829323923/20000000000000 : ℝ), (50588589420787/100000000000000 : ℝ), (697226394153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036769469/2000000000 : ℝ)|^4387 ≤ (8487829323923/20000000000000 : ℝ)^3363
        have hw : |(1036769469/2000000000 : ℝ)|=(1036769469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1186210329/2000000000 : ℝ)|^4387 ≤ (50588589420787/100000000000000 : ℝ)^3363
        have hw : |(1186210329/2000000000 : ℝ)|=(1186210329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-649112447/5000000000 : ℝ)|^4387 ≤ (697226394153/10000000000000 : ℝ)^3363
        have hw : |(-649112447/5000000000 : ℝ)|=(649112447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s0_7 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417499479/1000000000 : ℝ)*x 0 + (5484150011/10000000000 : ℝ)*x 1 + (3168162377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417499479/1000000000 : ℝ)^4387 ≤ (15999980525557/50000000000000 : ℝ)^3363 := by
    have hnat : (417499479 : ℕ)^4387*50000000000000^3363 ≤ 15999980525557^3363*1000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417499479 1000000000 15999980525557 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484150011/10000000000 : ℝ)^4387 ≤ (45674175288687/100000000000000 : ℝ)^3363 := by
    have hnat : (5484150011 : ℕ)^4387*100000000000000^3363 ≤ 45674175288687^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484150011 10000000000 45674175288687 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168162377/10000000000 : ℝ)^4387 ≤ (2232586364813/10000000000000 : ℝ)^3363 := by
    have hnat : (3168162377 : ℕ)^4387*10000000000000^3363 ≤ 2232586364813^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168162377 10000000000 2232586364813 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417499479/1000000000 : ℝ), (5484150011/10000000000 : ℝ), (3168162377/10000000000 : ℝ)] ![(15999980525557/50000000000000 : ℝ), (45674175288687/100000000000000 : ℝ), (2232586364813/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417499479/1000000000 : ℝ)|^4387 ≤ (15999980525557/50000000000000 : ℝ)^3363
        have hw : |(417499479/1000000000 : ℝ)|=(417499479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484150011/10000000000 : ℝ)|^4387 ≤ (45674175288687/100000000000000 : ℝ)^3363
        have hw : |(5484150011/10000000000 : ℝ)|=(5484150011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168162377/10000000000 : ℝ)|^4387 ≤ (2232586364813/10000000000000 : ℝ)^3363
        have hw : |(3168162377/10000000000 : ℝ)|=(3168162377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1427_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1017/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (821/3125 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2193/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2193 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2193*1^512 ≤ 0^512*1^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2193/512 : ℝ) ≤ (78995454586353439/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2193 ≤ (78995454586353439/4000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2193*4000000000000000000^512 ≤ 78995454586353439^512*5^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 78995454586353439 4000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (78995454586353439/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2193 := by
      have hnat : (1 : ℕ)^512*1^2193 ≤ 1^2193*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4078995454586353439/4000000000000000000 : ℝ) ≤ (2511440677633697/2500000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (4078995454586353439/4000000000000000000 : ℝ)^512 ≤ (2511440677633697/2500000000000000 : ℝ)^2193 := by
      have hnat : (4078995454586353439 : ℕ)^512*2500000000000000^2193 ≤ 2511440677633697^2193*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4078995454586353439 4000000000000000000 2511440677633697 2500000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511440677633697/2500000000000000 : ℝ)) (X := (4078995454586353439/4000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2078995454586353439/2000000000000000000 : ℝ) ≤ (1261440677633697/1250000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (2078995454586353439/2000000000000000000 : ℝ)^512 ≤ (1261440677633697/1250000000000000 : ℝ)^2193 := by
      have hnat : (2078995454586353439 : ℕ)^512*1250000000000000^2193 ≤ 1261440677633697^2193*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2078995454586353439 2000000000000000000 1261440677633697 1250000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261440677633697/1250000000000000 : ℝ)) (X := (2078995454586353439/2000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11440677633697/1000000000000000 : ℝ)*(0 : ℝ))^(2193/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(11440677633697/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78995454586353439/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11440677633697/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2193/512 : ℝ) := by
    rw [show (1 : ℝ)+(11440677633697/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511440677633697/2500000000000000 : ℝ) by norm_num, show 1+(78995454586353439/4000000000000000000 : ℝ)+(0 : ℝ)=(4078995454586353439/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78995454586353439/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11440677633697/1000000000000000 : ℝ)*(2/5 : ℝ))^(2193/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(11440677633697/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261440677633697/1250000000000000 : ℝ) by norm_num, show 1+2*(78995454586353439/4000000000000000000 : ℝ)=(2078995454586353439/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11440677633697/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11440677633697/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11440677633697/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11440677633697/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11440677633697/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11440677633697/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1759946687/10000000000 : ℝ)*X 0 0+(372562917/625000000 : ℝ)*X 0 1+(1207695129/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5492321629/10000000000 : ℝ)*X 1 0+(-23984961/100000000 : ℝ)*X 1 1+(4830780947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((343270131/625000000 : ℝ)*X 2 0+(2415390383/5000000000 : ℝ)*X 2 1+(-1199247861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166287627/10000000000 : ℝ)*X 0 0+(1551703399/5000000000 : ℝ)*X 0 1+(5546673099/10000000000 : ℝ)*X 0 2+(4166287627/10000000000 : ℝ)*X 1 0+(1551703399/5000000000 : ℝ)*X 1 1+(5546673099/10000000000 : ℝ)*X 1 2+(4166287627/10000000000 : ℝ)*X 2 0+(1551703399/5000000000 : ℝ)*X 2 1+(5546673099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1763973523/10000000000 : ℝ)*X 0 0+(4859702849/10000000000 : ℝ)*X 0 1+(5931051733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((207353893/400000000 : ℝ)*X 1 0+(-259644933/2000000000 : ℝ)*X 1 1+(5931051809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1036769469/2000000000 : ℝ)*X 2 0+(1186210329/2000000000 : ℝ)*X 2 1+(-649112447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((417499479/1000000000 : ℝ)*X 0 0+(5484150011/10000000000 : ℝ)*X 0 1+(3168162377/10000000000 : ℝ)*X 0 2+(417499479/1000000000 : ℝ)*X 1 0+(5484150011/10000000000 : ℝ)*X 1 1+(3168162377/10000000000 : ℝ)*X 1 2+(417499479/1000000000 : ℝ)*X 2 0+(5484150011/10000000000 : ℝ)*X 2 1+(3168162377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62896744491427521037503/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107250231/25000000000000 : ℝ)*(base19) + (202445111/50000000000000 : ℝ)*(base23) + (574493/1250000000000 : ℝ)*(upper3) + (54561669/100000000000000 : ℝ)*(upper4) + (20243431/25000000000000 : ℝ)*(upper5) + (647035867966533/100000000000000 : ℝ)*(major0) + (647035867966533/100000000000000 : ℝ)*(major1) + (647035867966533/100000000000000 : ℝ)*(major2) + (884779955657413/100000000000000 : ℝ)*(sp0) + (884781471037403/100000000000000 : ℝ)*(sp1) + (176956299029621/20000000000000 : ℝ)*(sp2) + (409288977152867/100000000000000 : ℝ)*(sp3) + (972190457/50000000000000 : ℝ)*(sp4) + (816810707/100000000000000 : ℝ)*(sp7) + (204644896981787/50000000000000 : ℝ)*(f.failure) + (884781900038327/100000000000000 : ℝ)*(f.sum) + (49314990237499/50000000000000000000000000000 : ℝ)*base66 + (213461512562501/100000000000000000000000000000 : ℝ)*base67 + (193812815137499/100000000000000000000000000000 : ℝ)*base70 + (278292633537499/100000000000000000000000000000 : ℝ)*base72 + (46169161912501/50000000000000000000000000000 : ℝ)*base73 + (360830027762501/100000000000000000000000000000 : ℝ)*base75 + (110206492837499/100000000000000000000000000000 : ℝ)*base78 + (452555021762501/100000000000000000000000000000 : ℝ)*base79 + (83158799037499/50000000000000000000000000000 : ℝ)*base82 + (1963529/5000000000000000000000 : ℝ)*base89 + (1963529/5000000000000000000000 : ℝ)*base91 + (1963529/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6864043112855878107/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1564240977/100000000000000 : ℝ)*(base19) + (394128867/25000000000000 : ℝ)*(base23) + (32598931/20000000000000 : ℝ)*(base32) + (23801589/10000000000000 : ℝ)*(upper3) + (134404491/100000000000000 : ℝ)*(upper5) + (170647906163251/25000000000000 : ℝ)*(major0) + (170647906163251/25000000000000 : ℝ)*(major1) + (170647906163251/25000000000000 : ℝ)*(major2) + (73719941/2000000000000 : ℝ)*(sp1) + (3831744573/100000000000000 : ℝ)*(sp2) + (933402033936541/100000000000000 : ℝ)*(sp4) + (466698391849257/50000000000000 : ℝ)*(sp5) + (1866793251353/200000000000 : ℝ)*(sp6) + (107945205893343/25000000000000 : ℝ)*(sp7) + (431780986568027/100000000000000 : ℝ)*(f.failure) + (933402033936541/100000000000000 : ℝ)*(f.sum) + (13553738543553/12500000000000000000000000000 : ℝ)*base66 + (127752550643947/25000000000000000000000000000 : ℝ)*base67 + (224334659256053/25000000000000000000000000000 : ℝ)*base70 + (9320326168947/25000000000000000000000000000 : ℝ)*base71 + (39178432143947/12500000000000000000000000000 : ℝ)*base73 + (141795724831053/25000000000000000000000000000 : ℝ)*base76 + (1337625968947/25000000000000000000000000000 : ℝ)*base77 + (1422047918947/25000000000000000000000000000 : ℝ)*base79 + (42864858556053/12500000000000000000000000000 : ℝ)*base82 + (11617609/10000000000000000000000 : ℝ)*base89 + (11617609/10000000000000000000000 : ℝ)*base91 + (11617609/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1427_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1017/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (821/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1427_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1427_s1_0 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-386516933/2000000000 : ℝ)*x 0 + (5606027427/10000000000 : ℝ)*x 1 + (317193047/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (386516933/2000000000 : ℝ)^4387 ≤ (11715877503781/100000000000000 : ℝ)^3363 := by
    have hnat : (386516933 : ℕ)^4387*100000000000000^3363 ≤ 11715877503781^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386516933 2000000000 11715877503781 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5606027427/10000000000 : ℝ)^4387 ≤ (11750686628887/25000000000000 : ℝ)^3363 := by
    have hnat : (5606027427 : ℕ)^4387*25000000000000^3363 ≤ 11750686628887^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606027427 10000000000 11750686628887 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317193047/625000000 : ℝ)^4387 ≤ (41281375966427/100000000000000 : ℝ)^3363 := by
    have hnat : (317193047 : ℕ)^4387*100000000000000^3363 ≤ 41281375966427^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317193047 625000000 41281375966427 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-386516933/2000000000 : ℝ), (5606027427/10000000000 : ℝ), (317193047/625000000 : ℝ)] ![(11715877503781/100000000000000 : ℝ), (11750686628887/25000000000000 : ℝ), (41281375966427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-386516933/2000000000 : ℝ)|^4387 ≤ (11715877503781/100000000000000 : ℝ)^3363
        have hw : |(-386516933/2000000000 : ℝ)|=(386516933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5606027427/10000000000 : ℝ)|^4387 ≤ (11750686628887/25000000000000 : ℝ)^3363
        have hw : |(5606027427/10000000000 : ℝ)|=(5606027427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317193047/625000000 : ℝ)|^4387 ≤ (41281375966427/100000000000000 : ℝ)^3363
        have hw : |(317193047/625000000 : ℝ)|=(317193047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s1_1 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349252743/2500000000 : ℝ)*x 0 + (-138372811/625000000 : ℝ)*x 1 + (5075090049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349252743/2500000000 : ℝ)^4387 ≤ (11182442093087/25000000000000 : ℝ)^3363 := by
    have hnat : (1349252743 : ℕ)^4387*25000000000000^3363 ≤ 11182442093087^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349252743 2500000000 11182442093087 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138372811/625000000 : ℝ)^4387 ≤ (6994420943319/50000000000000 : ℝ)^3363 := by
    have hnat : (138372811 : ℕ)^4387*50000000000000^3363 ≤ 6994420943319^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138372811 625000000 6994420943319 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075090049/10000000000 : ℝ)^4387 ≤ (1290043429023/3125000000000 : ℝ)^3363 := by
    have hnat : (5075090049 : ℕ)^4387*3125000000000^3363 ≤ 1290043429023^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075090049 10000000000 1290043429023 3125000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349252743/2500000000 : ℝ), (-138372811/625000000 : ℝ), (5075090049/10000000000 : ℝ)] ![(11182442093087/25000000000000 : ℝ), (6994420943319/50000000000000 : ℝ), (1290043429023/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349252743/2500000000 : ℝ)|^4387 ≤ (11182442093087/25000000000000 : ℝ)^3363
        have hw : |(1349252743/2500000000 : ℝ)|=(1349252743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138372811/625000000 : ℝ)|^4387 ≤ (6994420943319/50000000000000 : ℝ)^3363
        have hw : |(-138372811/625000000 : ℝ)|=(138372811/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075090049/10000000000 : ℝ)|^4387 ≤ (1290043429023/3125000000000 : ℝ)^3363
        have hw : |(5075090049/10000000000 : ℝ)|=(5075090049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s1_2 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397011983/10000000000 : ℝ)*x 0 + (1268772229/2500000000 : ℝ)*x 1 + (-553491277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397011983/10000000000 : ℝ)^4387 ≤ (5591222412841/12500000000000 : ℝ)^3363 := by
    have hnat : (5397011983 : ℕ)^4387*12500000000000^3363 ≤ 5591222412841^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397011983 10000000000 5591222412841 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268772229/2500000000 : ℝ)^4387 ≤ (41281377706611/100000000000000 : ℝ)^3363 := by
    have hnat : (1268772229 : ℕ)^4387*100000000000000^3363 ≤ 41281377706611^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268772229 2500000000 41281377706611 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553491277/2500000000 : ℝ)^4387 ≤ (1398884297463/10000000000000 : ℝ)^3363 := by
    have hnat : (553491277 : ℕ)^4387*10000000000000^3363 ≤ 1398884297463^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553491277 2500000000 1398884297463 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397011983/10000000000 : ℝ), (1268772229/2500000000 : ℝ), (-553491277/2500000000 : ℝ)] ![(5591222412841/12500000000000 : ℝ), (41281377706611/100000000000000 : ℝ), (1398884297463/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397011983/10000000000 : ℝ)|^4387 ≤ (5591222412841/12500000000000 : ℝ)^3363
        have hw : |(5397011983/10000000000 : ℝ)|=(5397011983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1268772229/2500000000 : ℝ)|^4387 ≤ (41281377706611/100000000000000 : ℝ)^3363
        have hw : |(1268772229/2500000000 : ℝ)|=(1268772229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553491277/2500000000 : ℝ)|^4387 ≤ (1398884297463/10000000000000 : ℝ)^3363
        have hw : |(-553491277/2500000000 : ℝ)|=(553491277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s1_3 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855400459/2000000000 : ℝ)*x 0 + (934380893/2500000000 : ℝ)*x 1 + (4885277521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855400459/2000000000 : ℝ)^4387 ≤ (16511827187079/50000000000000 : ℝ)^3363 := by
    have hnat : (855400459 : ℕ)^4387*50000000000000^3363 ≤ 16511827187079^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855400459 2000000000 16511827187079 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934380893/2500000000 : ℝ)^4387 ≤ (13848732041051/50000000000000 : ℝ)^3363 := by
    have hnat : (934380893 : ℕ)^4387*50000000000000^3363 ≤ 13848732041051^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934380893 2500000000 13848732041051 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4885277521/10000000000 : ℝ)^4387 ≤ (3927888152443/10000000000000 : ℝ)^3363 := by
    have hnat : (4885277521 : ℕ)^4387*10000000000000^3363 ≤ 3927888152443^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885277521 10000000000 3927888152443 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855400459/2000000000 : ℝ), (934380893/2500000000 : ℝ), (4885277521/10000000000 : ℝ)] ![(16511827187079/50000000000000 : ℝ), (13848732041051/50000000000000 : ℝ), (3927888152443/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855400459/2000000000 : ℝ)|^4387 ≤ (16511827187079/50000000000000 : ℝ)^3363
        have hw : |(855400459/2000000000 : ℝ)|=(855400459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(934380893/2500000000 : ℝ)|^4387 ≤ (13848732041051/50000000000000 : ℝ)^3363
        have hw : |(934380893/2500000000 : ℝ)|=(934380893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4885277521/10000000000 : ℝ)|^4387 ≤ (3927888152443/10000000000000 : ℝ)^3363
        have hw : |(4885277521/10000000000 : ℝ)|=(4885277521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s1_4 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-241623173/1250000000 : ℝ)*x 0 + (508132447/1000000000 : ℝ)*x 1 + (5599685821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241623173/1250000000 : ℝ)^4387 ≤ (2929761641387/25000000000000 : ℝ)^3363 := by
    have hnat : (241623173 : ℕ)^4387*25000000000000^3363 ≤ 2929761641387^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241623173 1250000000 2929761641387 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508132447/1000000000 : ℝ)^4387 ≤ (20673777389171/50000000000000 : ℝ)^3363 := by
    have hnat : (508132447 : ℕ)^4387*50000000000000^3363 ≤ 20673777389171^3363*1000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508132447 1000000000 20673777389171 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5599685821/10000000000 : ℝ)^4387 ≤ (9386679726121/20000000000000 : ℝ)^3363 := by
    have hnat : (5599685821 : ℕ)^4387*20000000000000^3363 ≤ 9386679726121^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5599685821 10000000000 9386679726121 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-241623173/1250000000 : ℝ), (508132447/1000000000 : ℝ), (5599685821/10000000000 : ℝ)] ![(2929761641387/25000000000000 : ℝ), (20673777389171/50000000000000 : ℝ), (9386679726121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-241623173/1250000000 : ℝ)|^4387 ≤ (2929761641387/25000000000000 : ℝ)^3363
        have hw : |(-241623173/1250000000 : ℝ)|=(241623173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508132447/1000000000 : ℝ)|^4387 ≤ (20673777389171/50000000000000 : ℝ)^3363
        have hw : |(508132447/1000000000 : ℝ)|=(508132447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5599685821/10000000000 : ℝ)|^4387 ≤ (9386679726121/20000000000000 : ℝ)^3363
        have hw : |(5599685821/10000000000 : ℝ)|=(5599685821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s1_5 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328644499/625000000 : ℝ)*x 0 + (-84468431/500000000 : ℝ)*x 1 + (1119937167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328644499/625000000 : ℝ)^4387 ≤ (21618066504587/50000000000000 : ℝ)^3363 := by
    have hnat : (328644499 : ℕ)^4387*50000000000000^3363 ≤ 21618066504587^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328644499 625000000 21618066504587 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84468431/500000000 : ℝ)^4387 ≤ (4915234099181/50000000000000 : ℝ)^3363 := by
    have hnat : (84468431 : ℕ)^4387*50000000000000^3363 ≤ 4915234099181^3363*500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84468431 500000000 4915234099181 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119937167/2000000000 : ℝ)^4387 ≤ (23466699391837/50000000000000 : ℝ)^3363 := by
    have hnat : (1119937167 : ℕ)^4387*50000000000000^3363 ≤ 23466699391837^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119937167 2000000000 23466699391837 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328644499/625000000 : ℝ), (-84468431/500000000 : ℝ), (1119937167/2000000000 : ℝ)] ![(21618066504587/50000000000000 : ℝ), (4915234099181/50000000000000 : ℝ), (23466699391837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328644499/625000000 : ℝ)|^4387 ≤ (21618066504587/50000000000000 : ℝ)^3363
        have hw : |(328644499/625000000 : ℝ)|=(328644499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84468431/500000000 : ℝ)|^4387 ≤ (4915234099181/50000000000000 : ℝ)^3363
        have hw : |(-84468431/500000000 : ℝ)|=(84468431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119937167/2000000000 : ℝ)|^4387 ≤ (23466699391837/50000000000000 : ℝ)^3363
        have hw : |(1119937167/2000000000 : ℝ)|=(1119937167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s1_6 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262915597/500000000 : ℝ)*x 0 + (2799842899/5000000000 : ℝ)*x 1 + (-337873747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262915597/500000000 : ℝ)^4387 ≤ (21618066268613/50000000000000 : ℝ)^3363 := by
    have hnat : (262915597 : ℕ)^4387*50000000000000^3363 ≤ 21618066268613^3363*500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262915597 500000000 21618066268613 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2799842899/5000000000 : ℝ)^4387 ≤ (23466699189567/50000000000000 : ℝ)^3363 := by
    have hnat : (2799842899 : ℕ)^4387*50000000000000^3363 ≤ 23466699189567^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799842899 5000000000 23466699189567 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337873747/2000000000 : ℝ)^4387 ≤ (983046907131/10000000000000 : ℝ)^3363 := by
    have hnat : (337873747 : ℕ)^4387*10000000000000^3363 ≤ 983046907131^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337873747 2000000000 983046907131 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262915597/500000000 : ℝ), (2799842899/5000000000 : ℝ), (-337873747/2000000000 : ℝ)] ![(21618066268613/50000000000000 : ℝ), (23466699189567/50000000000000 : ℝ), (983046907131/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262915597/500000000 : ℝ)|^4387 ≤ (21618066268613/50000000000000 : ℝ)^3363
        have hw : |(262915597/500000000 : ℝ)|=(262915597/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2799842899/5000000000 : ℝ)|^4387 ≤ (23466699189567/50000000000000 : ℝ)^3363
        have hw : |(2799842899/5000000000 : ℝ)|=(2799842899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337873747/2000000000 : ℝ)|^4387 ≤ (983046907131/10000000000000 : ℝ)^3363
        have hw : |(-337873747/2000000000 : ℝ)|=(337873747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s1_7 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138934487/5000000000 : ℝ)*x 0 + (4871798501/10000000000 : ℝ)*x 1 + (75024619/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138934487/5000000000 : ℝ)^4387 ≤ (33032384049349/100000000000000 : ℝ)^3363 := by
    have hnat : (2138934487 : ℕ)^4387*100000000000000^3363 ≤ 33032384049349^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138934487 5000000000 33032384049349 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4871798501/10000000000 : ℝ)^4387 ≤ (39137567139639/100000000000000 : ℝ)^3363 := by
    have hnat : (4871798501 : ℕ)^4387*100000000000000^3363 ≤ 39137567139639^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871798501 10000000000 39137567139639 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75024619/200000000 : ℝ)^4387 ≤ (27830048791973/100000000000000 : ℝ)^3363 := by
    have hnat : (75024619 : ℕ)^4387*100000000000000^3363 ≤ 27830048791973^3363*200000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75024619 200000000 27830048791973 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138934487/5000000000 : ℝ), (4871798501/10000000000 : ℝ), (75024619/200000000 : ℝ)] ![(33032384049349/100000000000000 : ℝ), (39137567139639/100000000000000 : ℝ), (27830048791973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138934487/5000000000 : ℝ)|^4387 ≤ (33032384049349/100000000000000 : ℝ)^3363
        have hw : |(2138934487/5000000000 : ℝ)|=(2138934487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4871798501/10000000000 : ℝ)|^4387 ≤ (39137567139639/100000000000000 : ℝ)^3363
        have hw : |(4871798501/10000000000 : ℝ)|=(4871798501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75024619/200000000 : ℝ)|^4387 ≤ (27830048791973/100000000000000 : ℝ)^3363
        have hw : |(75024619/200000000 : ℝ)|=(75024619/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1427_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (821/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1017/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1527/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (943/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (821/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1017/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (821/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1017/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (821/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1017/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (821/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1017/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (821/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1017/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (821/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1017/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1017/50000 : ℝ) ^ (2193/512 : ℝ) ≤ (2839837573103/50000000000000000000 : ℝ) := by
    have hpowers : (1017/50000 : ℝ)^2193 ≤ (2839837573103/50000000000000000000 : ℝ)^512 := by
      have hnat : (1017 : ℕ)^2193*50000000000000000000^512 ≤ 2839837573103^512*50000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1017 50000 2839837573103 50000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1017/50000 : ℝ)) (X := (2839837573103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hpowhi : (821/3125 : ℝ) ^ (2193/512 : ℝ) ≤ (163132761503894801/50000000000000000000 : ℝ) := by
    have hpowers : (821/3125 : ℝ)^2193 ≤ (163132761503894801/50000000000000000000 : ℝ)^512 := by
      have hnat : (821 : ℕ)^2193*50000000000000000000^512 ≤ 163132761503894801^512*3125^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        821 3125 163132761503894801 50000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (821/3125 : ℝ)) (X := (163132761503894801/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000002839837573103/25000000000000000000 : ℝ) ≤ (1000000026520689/1000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (25000002839837573103/25000000000000000000 : ℝ)^512 ≤ (1000000026520689/1000000000000000 : ℝ)^2193 := by
      have hnat : (25000002839837573103 : ℕ)^512*1000000000000000^2193 ≤ 1000000026520689^2193*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000002839837573103 25000000000000000000 1000000026520689 1000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000026520689/1000000000000000 : ℝ)) (X := (25000002839837573103/25000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (195949748442740109/195312500000000000 : ℝ) ≤ (5003803975420197/5000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (195949748442740109/195312500000000000 : ℝ)^512 ≤ (5003803975420197/5000000000000000 : ℝ)^2193 := by
      have hnat : (195949748442740109 : ℕ)^512*5000000000000000^2193 ≤ 5003803975420197^2193*195312500000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195949748442740109 195312500000000000 5003803975420197 5000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003803975420197/5000000000000000 : ℝ)) (X := (195949748442740109/195312500000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25163132761503894801/25000000000000000000 : ℝ) ≤ (5007607818236949/5000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (25163132761503894801/25000000000000000000 : ℝ)^512 ≤ (5007607818236949/5000000000000000 : ℝ)^2193 := by
      have hnat : (25163132761503894801 : ℕ)^512*5000000000000000^2193 ≤ 5007607818236949^2193*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25163132761503894801 25000000000000000000 5007607818236949 5000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007607818236949/5000000000000000 : ℝ)) (X := (25163132761503894801/25000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2839837573103/50000000000000000000 : ℝ) ≤ ((60587264590731876387/60595000000000000000 : ℝ)+2*(237740176047/75743750000000 : ℝ)*(1017/50000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (60587264590731876387/60595000000000000000 : ℝ)+2*(237740176047/75743750000000 : ℝ)*(1017/50000 : ℝ)=(1000000026520689/1000000000000000 : ℝ) by norm_num, show 1+2*(2839837573103/50000000000000000000 : ℝ)=(25000002839837573103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(163132761503894801/50000000000000000000 : ℝ)+(2839837573103/50000000000000000000 : ℝ) ≤ ((60587264590731876387/60595000000000000000 : ℝ)+(237740176047/75743750000000 : ℝ)*((821/3125 : ℝ)+(1017/50000 : ℝ)))^(2193/512 : ℝ) := by
    rw [show (60587264590731876387/60595000000000000000 : ℝ)+(237740176047/75743750000000 : ℝ)*((821/3125 : ℝ)+(1017/50000 : ℝ))=(5003803975420197/5000000000000000 : ℝ) by norm_num, show 1+(163132761503894801/50000000000000000000 : ℝ)+(2839837573103/50000000000000000000 : ℝ)=(195949748442740109/195312500000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(163132761503894801/50000000000000000000 : ℝ) ≤ ((60587264590731876387/60595000000000000000 : ℝ)+2*(237740176047/75743750000000 : ℝ)*(821/3125 : ℝ))^(2193/512 : ℝ) := by
    rw [show (60587264590731876387/60595000000000000000 : ℝ)+2*(237740176047/75743750000000 : ℝ)*(821/3125 : ℝ)=(5007607818236949/5000000000000000 : ℝ) by norm_num, show 1+2*(163132761503894801/50000000000000000000 : ℝ)=(25163132761503894801/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60587264590731876387/60595000000000000000 : ℝ)*(X 1 0+X 2 0)+(237740176047/75743750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (1017/50000 : ℝ)) (hi := (821/3125 : ℝ)) (c := (60587264590731876387/60595000000000000000 : ℝ)) (alpha := (237740176047/75743750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60587264590731876387/60595000000000000000 : ℝ)*(X 0 1+X 2 1)+(237740176047/75743750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (1017/50000 : ℝ)) (hi := (821/3125 : ℝ)) (c := (60587264590731876387/60595000000000000000 : ℝ)) (alpha := (237740176047/75743750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60587264590731876387/60595000000000000000 : ℝ)*(X 0 2+X 1 2)+(237740176047/75743750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (1017/50000 : ℝ)) (hi := (821/3125 : ℝ)) (c := (60587264590731876387/60595000000000000000 : ℝ)) (alpha := (237740176047/75743750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-386516933/2000000000 : ℝ)*X 0 0+(5606027427/10000000000 : ℝ)*X 0 1+(317193047/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1349252743/2500000000 : ℝ)*X 1 0+(-138372811/625000000 : ℝ)*X 1 1+(5075090049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5397011983/10000000000 : ℝ)*X 2 0+(1268772229/2500000000 : ℝ)*X 2 1+(-553491277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((855400459/2000000000 : ℝ)*X 0 0+(934380893/2500000000 : ℝ)*X 0 1+(4885277521/10000000000 : ℝ)*X 0 2+(855400459/2000000000 : ℝ)*X 1 0+(934380893/2500000000 : ℝ)*X 1 1+(4885277521/10000000000 : ℝ)*X 1 2+(855400459/2000000000 : ℝ)*X 2 0+(934380893/2500000000 : ℝ)*X 2 1+(4885277521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-241623173/1250000000 : ℝ)*X 0 0+(508132447/1000000000 : ℝ)*X 0 1+(5599685821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328644499/625000000 : ℝ)*X 1 0+(-84468431/500000000 : ℝ)*X 1 1+(1119937167/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262915597/500000000 : ℝ)*X 2 0+(2799842899/5000000000 : ℝ)*X 2 1+(-337873747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2138934487/5000000000 : ℝ)*X 0 0+(4871798501/10000000000 : ℝ)*X 0 1+(75024619/200000000 : ℝ)*X 0 2+(2138934487/5000000000 : ℝ)*X 1 0+(4871798501/10000000000 : ℝ)*X 1 1+(75024619/200000000 : ℝ)*X 1 2+(2138934487/5000000000 : ℝ)*X 2 0+(4871798501/10000000000 : ℝ)*X 2 1+(75024619/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5551126038967319372422229031/757437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2975207/100000000000000 : ℝ)*(base1) + (1208902269/100000000000000 : ℝ)*(base19) + (1561726981/100000000000000 : ℝ)*(base23) + (13396611/10000000000000 : ℝ)*(upper3) + (152435157/100000000000000 : ℝ)*(upper5) + (344344914317671/25000000000000 : ℝ)*(major0) + (344344914317671/25000000000000 : ℝ)*(major1) + (344344914317671/25000000000000 : ℝ)*(major2) + (470867175527547/25000000000000 : ℝ)*(sp0) + (470870228395927/25000000000000 : ℝ)*(sp1) + (470870140189749/25000000000000 : ℝ)*(sp2) + (871271697786233/100000000000000 : ℝ)*(sp3) + (3355837749/25000000000000 : ℝ)*(sp4) + (655874977/12500000000000 : ℝ)*(sp7) + (871276947761257/100000000000000 : ℝ)*(f.failure) + (1883482122485977/100000000000000 : ℝ)*(f.sum) + (274795727197543/60595000000000000000000000000 : ℝ)*base65 + (429669099157665323/1514875000000000000000000000000000 : ℝ)*base68 + (5891775411588040323/1514875000000000000000000000000000 : ℝ)*base70 + (2523580914638209677/1514875000000000000000000000000000 : ℝ)*base71 + (70776657863347/15148750000000000000000000000 : ℝ)*base73 + (4389759579513040323/1514875000000000000000000000000000 : ℝ)*base76 + (5157751671130290323/1514875000000000000000000000000000 : ℝ)*base78 + (10069793277984834677/1514875000000000000000000000000000 : ℝ)*base79 + (247591117793493/60595000000000000000000000000 : ℝ)*base81 + (39866019/10000000000000000000000 : ℝ)*base89 + (39866019/10000000000000000000000 : ℝ)*base91 + (39866019/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29275524402292587178832020839/3029750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43314743/50000000000000 : ℝ)*(base1) + (248429991/12500000000000 : ℝ)*(base19) + (1963862203/100000000000000 : ℝ)*(base23) + (22961499/10000000000000 : ℝ)*(upper3) + (26311483/12500000000000 : ℝ)*(upper5) + (352695146426459/25000000000000 : ℝ)*(major0) + (352695146426459/25000000000000 : ℝ)*(major1) + (1410780585705837/100000000000000 : ℝ)*(major2) + (2855112737/25000000000000 : ℝ)*(sp1) + (11138487671/100000000000000 : ℝ)*(sp2) + (1929155856359913/100000000000000 : ℝ)*(sp4) + (1929142361839551/100000000000000 : ℝ)*(sp5) + (241142833422569/12500000000000 : ℝ)*(sp6) + (223101248240551/25000000000000 : ℝ)*(sp7) + (89240507959169/10000000000000 : ℝ)*(f.failure) + (1929155769730427/100000000000000 : ℝ)*(f.sum) + (3797619924229/7574375000000000000000000000 : ℝ)*base66 + (14269000087253826367/1514875000000000000000000000000000 : ℝ)*base68 + (40282325083368470919/6059500000000000000000000000000000 : ℝ)*base69 + (10293531836581076367/1514875000000000000000000000000000 : ℝ)*base72 + (15119208283867/3787187500000000000000000000 : ℝ)*base74 + (27763501313010470919/6059500000000000000000000000000000 : ℝ)*base75 + (3083936535193648633/1514875000000000000000000000000000 : ℝ)*base77 + (5131230842790476367/1514875000000000000000000000000000 : ℝ)*base80 + (24147012505133/15148750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6634923/1000000000000000000000 : ℝ)*base89 + (6634923/1000000000000000000000 : ℝ)*base91 + (3365077/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1427_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (821/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1017/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1527/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (943/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1427_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1427_s2_0 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-982932723/5000000000 : ℝ)*x 0 + (5458627323/10000000000 : ℝ)*x 1 + (1300267223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982932723/5000000000 : ℝ)^4387 ≤ (748734719893/6250000000000 : ℝ)^3363 := by
    have hnat : (982932723 : ℕ)^4387*6250000000000^3363 ≤ 748734719893^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982932723 5000000000 748734719893 6250000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458627323/10000000000 : ℝ)^4387 ≤ (45397085569121/100000000000000 : ℝ)^3363 := by
    have hnat : (5458627323 : ℕ)^4387*100000000000000^3363 ≤ 45397085569121^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458627323 10000000000 45397085569121 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300267223/2500000000 : ℝ)^4387 ≤ (5327894862143/12500000000000 : ℝ)^3363 := by
    have hnat : (1300267223 : ℕ)^4387*12500000000000^3363 ≤ 5327894862143^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300267223 2500000000 5327894862143 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-982932723/5000000000 : ℝ), (5458627323/10000000000 : ℝ), (1300267223/2500000000 : ℝ)] ![(748734719893/6250000000000 : ℝ), (45397085569121/100000000000000 : ℝ), (5327894862143/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-982932723/5000000000 : ℝ)|^4387 ≤ (748734719893/6250000000000 : ℝ)^3363
        have hw : |(-982932723/5000000000 : ℝ)|=(982932723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458627323/10000000000 : ℝ)|^4387 ≤ (45397085569121/100000000000000 : ℝ)^3363
        have hw : |(5458627323/10000000000 : ℝ)|=(5458627323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300267223/2500000000 : ℝ)|^4387 ≤ (5327894862143/12500000000000 : ℝ)^3363
        have hw : |(1300267223/2500000000 : ℝ)|=(1300267223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s2_1 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340067259/2500000000 : ℝ)*x 0 + (-1049194973/5000000000 : ℝ)*x 1 + (1300267199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340067259/2500000000 : ℝ)^4387 ≤ (1108323674493/2500000000000 : ℝ)^3363 := by
    have hnat : (1340067259 : ℕ)^4387*2500000000000^3363 ≤ 1108323674493^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340067259 2500000000 1108323674493 2500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049194973/5000000000 : ℝ)^4387 ≤ (13043895132249/100000000000000 : ℝ)^3363 := by
    have hnat : (1049194973 : ℕ)^4387*100000000000000^3363 ≤ 13043895132249^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049194973 5000000000 13043895132249 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300267199/2500000000 : ℝ)^4387 ≤ (21311578935433/50000000000000 : ℝ)^3363 := by
    have hnat : (1300267199 : ℕ)^4387*50000000000000^3363 ≤ 21311578935433^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300267199 2500000000 21311578935433 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340067259/2500000000 : ℝ), (-1049194973/5000000000 : ℝ), (1300267199/2500000000 : ℝ)] ![(1108323674493/2500000000000 : ℝ), (13043895132249/100000000000000 : ℝ), (21311578935433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340067259/2500000000 : ℝ)|^4387 ≤ (1108323674493/2500000000000 : ℝ)^3363
        have hw : |(1340067259/2500000000 : ℝ)|=(1340067259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049194973/5000000000 : ℝ)|^4387 ≤ (13043895132249/100000000000000 : ℝ)^3363
        have hw : |(-1049194973/5000000000 : ℝ)|=(1049194973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300267199/2500000000 : ℝ)|^4387 ≤ (21311578935433/50000000000000 : ℝ)^3363
        have hw : |(1300267199/2500000000 : ℝ)|=(1300267199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s2_2 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670033583/1250000000 : ℝ)*x 0 + (2600534609/5000000000 : ℝ)*x 1 + (-419677977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670033583/1250000000 : ℝ)^4387 ≤ (5541617870777/12500000000000 : ℝ)^3363 := by
    have hnat : (670033583 : ℕ)^4387*12500000000000^3363 ≤ 5541617870777^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670033583 1250000000 5541617870777 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600534609/5000000000 : ℝ)^4387 ≤ (42623162382213/100000000000000 : ℝ)^3363 := by
    have hnat : (2600534609 : ℕ)^4387*100000000000000^3363 ≤ 42623162382213^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600534609 5000000000 42623162382213 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419677977/2000000000 : ℝ)^4387 ≤ (6521947318803/50000000000000 : ℝ)^3363 := by
    have hnat : (419677977 : ℕ)^4387*50000000000000^3363 ≤ 6521947318803^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419677977 2000000000 6521947318803 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670033583/1250000000 : ℝ), (2600534609/5000000000 : ℝ), (-419677977/2000000000 : ℝ)] ![(5541617870777/12500000000000 : ℝ), (42623162382213/100000000000000 : ℝ), (6521947318803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670033583/1250000000 : ℝ)|^4387 ≤ (5541617870777/12500000000000 : ℝ)^3363
        have hw : |(670033583/1250000000 : ℝ)|=(670033583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600534609/5000000000 : ℝ)|^4387 ≤ (42623162382213/100000000000000 : ℝ)^3363
        have hw : |(2600534609/5000000000 : ℝ)|=(2600534609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419677977/2000000000 : ℝ)|^4387 ≤ (6521947318803/50000000000000 : ℝ)^3363
        have hw : |(-419677977/2000000000 : ℝ)|=(419677977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s2_3 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537561303/1250000000 : ℝ)*x 0 + (2015098727/5000000000 : ℝ)*x 1 + (4586974277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537561303/1250000000 : ℝ)^4387 ≤ (3326043018549/10000000000000 : ℝ)^3363 := by
    have hnat : (537561303 : ℕ)^4387*10000000000000^3363 ≤ 3326043018549^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537561303 1250000000 3326043018549 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015098727/5000000000 : ℝ)^4387 ≤ (23874932473/78125000000 : ℝ)^3363 := by
    have hnat : (2015098727 : ℕ)^4387*78125000000^3363 ≤ 23874932473^3363*5000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015098727 5000000000 23874932473 78125000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4586974277/10000000000 : ℝ)^4387 ≤ (904491406021/2500000000000 : ℝ)^3363 := by
    have hnat : (4586974277 : ℕ)^4387*2500000000000^3363 ≤ 904491406021^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586974277 10000000000 904491406021 2500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537561303/1250000000 : ℝ), (2015098727/5000000000 : ℝ), (4586974277/10000000000 : ℝ)] ![(3326043018549/10000000000000 : ℝ), (23874932473/78125000000 : ℝ), (904491406021/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537561303/1250000000 : ℝ)|^4387 ≤ (3326043018549/10000000000000 : ℝ)^3363
        have hw : |(537561303/1250000000 : ℝ)|=(537561303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015098727/5000000000 : ℝ)|^4387 ≤ (23874932473/78125000000 : ℝ)^3363
        have hw : |(2015098727/5000000000 : ℝ)|=(2015098727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4586974277/10000000000 : ℝ)|^4387 ≤ (904491406021/2500000000000 : ℝ)^3363
        have hw : |(4586974277/10000000000 : ℝ)|=(4586974277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s2_4 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-491477857/2500000000 : ℝ)*x 0 + (162579541/312500000 : ℝ)*x 1 + (1091427731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491477857/2500000000 : ℝ)^4387 ≤ (11980121049391/100000000000000 : ℝ)^3363 := by
    have hnat : (491477857 : ℕ)^4387*100000000000000^3363 ≤ 11980121049391^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491477857 2500000000 11980121049391 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162579541/312500000 : ℝ)^4387 ≤ (1065973577343/2500000000000 : ℝ)^3363 := by
    have hnat : (162579541 : ℕ)^4387*2500000000000^3363 ≤ 1065973577343^3363*312500000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162579541 312500000 1065973577343 2500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091427731/2000000000 : ℝ)^4387 ≤ (181523743379/400000000000 : ℝ)^3363 := by
    have hnat : (1091427731 : ℕ)^4387*400000000000^3363 ≤ 181523743379^3363*2000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091427731 2000000000 181523743379 400000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491477857/2500000000 : ℝ), (162579541/312500000 : ℝ), (1091427731/2000000000 : ℝ)] ![(11980121049391/100000000000000 : ℝ), (1065973577343/2500000000000 : ℝ), (181523743379/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491477857/2500000000 : ℝ)|^4387 ≤ (11980121049391/100000000000000 : ℝ)^3363
        have hw : |(-491477857/2500000000 : ℝ)|=(491477857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162579541/312500000 : ℝ)|^4387 ≤ (1065973577343/2500000000000 : ℝ)^3363
        have hw : |(162579541/312500000 : ℝ)|=(162579541/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091427731/2000000000 : ℝ)|^4387 ≤ (181523743379/400000000000 : ℝ)^3363
        have hw : |(1091427731/2000000000 : ℝ)|=(1091427731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s2_5 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529330787/1000000000 : ℝ)*x 0 + (-115144991/625000000 : ℝ)*x 1 + (5457139039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529330787/1000000000 : ℝ)^4387 ≤ (5451485204413/12500000000000 : ℝ)^3363 := by
    have hnat : (529330787 : ℕ)^4387*12500000000000^3363 ≤ 5451485204413^3363*1000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529330787 1000000000 5451485204413 12500000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115144991/625000000 : ℝ)^4387 ≤ (11007178346061/100000000000000 : ℝ)^3363 := by
    have hnat : (115144991 : ℕ)^4387*100000000000000^3363 ≤ 11007178346061^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115144991 625000000 11007178346061 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457139039/10000000000 : ℝ)^4387 ≤ (22690470005189/50000000000000 : ℝ)^3363 := by
    have hnat : (5457139039 : ℕ)^4387*50000000000000^3363 ≤ 22690470005189^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457139039 10000000000 22690470005189 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529330787/1000000000 : ℝ), (-115144991/625000000 : ℝ), (5457139039/10000000000 : ℝ)] ![(5451485204413/12500000000000 : ℝ), (11007178346061/100000000000000 : ℝ), (22690470005189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529330787/1000000000 : ℝ)|^4387 ≤ (5451485204413/12500000000000 : ℝ)^3363
        have hw : |(529330787/1000000000 : ℝ)|=(529330787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115144991/625000000 : ℝ)|^4387 ≤ (11007178346061/100000000000000 : ℝ)^3363
        have hw : |(-115144991/625000000 : ℝ)|=(115144991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457139039/10000000000 : ℝ)|^4387 ≤ (22690470005189/50000000000000 : ℝ)^3363
        have hw : |(5457139039/10000000000 : ℝ)|=(5457139039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s2_6 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293307791/10000000000 : ℝ)*x 0 + (1364284753/2500000000 : ℝ)*x 1 + (-1842320003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293307791/10000000000 : ℝ)^4387 ≤ (4361188078623/10000000000000 : ℝ)^3363 := by
    have hnat : (5293307791 : ℕ)^4387*10000000000000^3363 ≤ 4361188078623^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293307791 10000000000 4361188078623 10000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364284753/2500000000 : ℝ)^4387 ≤ (22690469858741/50000000000000 : ℝ)^3363 := by
    have hnat : (1364284753 : ℕ)^4387*50000000000000^3363 ≤ 22690469858741^3363*2500000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364284753 2500000000 22690469858741 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842320003/10000000000 : ℝ)^4387 ≤ (2751794872939/25000000000000 : ℝ)^3363 := by
    have hnat : (1842320003 : ℕ)^4387*25000000000000^3363 ≤ 2751794872939^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842320003 10000000000 2751794872939 25000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293307791/10000000000 : ℝ), (1364284753/2500000000 : ℝ), (-1842320003/10000000000 : ℝ)] ![(4361188078623/10000000000000 : ℝ), (22690469858741/50000000000000 : ℝ), (2751794872939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293307791/10000000000 : ℝ)|^4387 ≤ (4361188078623/10000000000000 : ℝ)^3363
        have hw : |(5293307791/10000000000 : ℝ)|=(5293307791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364284753/2500000000 : ℝ)|^4387 ≤ (22690469858741/50000000000000 : ℝ)^3363
        have hw : |(1364284753/2500000000 : ℝ)|=(1364284753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1842320003/10000000000 : ℝ)|^4387 ≤ (2751794872939/25000000000000 : ℝ)^3363
        have hw : |(-1842320003/10000000000 : ℝ)|=(1842320003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1427_s2_7 (p : ℝ) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300589603/10000000000 : ℝ)*x 0 + (572972859/1250000000 : ℝ)*x 1 + (252088451/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300589603/10000000000 : ℝ)^4387 ≤ (6652286162349/20000000000000 : ℝ)^3363 := by
    have hnat : (4300589603 : ℕ)^4387*20000000000000^3363 ≤ 6652286162349^3363*10000000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300589603 10000000000 6652286162349 20000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572972859/1250000000 : ℝ)^4387 ≤ (18073411460129/50000000000000 : ℝ)^3363 := by
    have hnat : (572972859 : ℕ)^4387*50000000000000^3363 ≤ 18073411460129^3363*1250000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572972859 1250000000 18073411460129 50000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252088451/625000000 : ℝ)^4387 ≤ (30591746249607/100000000000000 : ℝ)^3363 := by
    have hnat : (252088451 : ℕ)^4387*100000000000000^3363 ≤ 30591746249607^3363*625000000^4387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252088451 625000000 30591746249607 100000000000000 4387 3363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4387/1024 : ℝ)) 4387 3363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300589603/10000000000 : ℝ), (572972859/1250000000 : ℝ), (252088451/625000000 : ℝ)] ![(6652286162349/20000000000000 : ℝ), (18073411460129/50000000000000 : ℝ), (30591746249607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300589603/10000000000 : ℝ)|^4387 ≤ (6652286162349/20000000000000 : ℝ)^3363
        have hw : |(4300589603/10000000000 : ℝ)|=(4300589603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572972859/1250000000 : ℝ)|^4387 ≤ (18073411460129/50000000000000 : ℝ)^3363
        have hw : |(572972859/1250000000 : ℝ)|=(572972859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252088451/625000000 : ℝ)|^4387 ≤ (30591746249607/100000000000000 : ℝ)^3363
        have hw : |(252088451/625000000 : ℝ)|=(252088451/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1427_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (943/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1527/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7903/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (943/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1527/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (943/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1527/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (943/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1527/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (943/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1527/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (943/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1527/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (943/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1527/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1527/20000 : ℝ) ^ (2193/512 : ℝ) ≤ (1640001309685953/100000000000000000000 : ℝ) := by
    have hpowers : (1527/20000 : ℝ)^2193 ≤ (1640001309685953/100000000000000000000 : ℝ)^512 := by
      have hnat : (1527 : ℕ)^2193*100000000000000000000^512 ≤ 1640001309685953^512*20000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1527 20000 1640001309685953 100000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1527/20000 : ℝ)) (X := (1640001309685953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hpowhi : (943/5000 : ℝ) ^ (2193/512 : ℝ) ≤ (39442814778667607/50000000000000000000 : ℝ) := by
    have hpowers : (943/5000 : ℝ)^2193 ≤ (39442814778667607/50000000000000000000 : ℝ)^512 := by
      have hnat : (943 : ℕ)^2193*50000000000000000000^512 ≤ 39442814778667607^512*5000^2193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        943 5000 39442814778667607 50000000000000000000 2193 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (943/5000 : ℝ)) (X := (39442814778667607/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001640001309685953/50000000000000000000 : ℝ) ≤ (16000122523683/16000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (50001640001309685953/50000000000000000000 : ℝ)^512 ≤ (16000122523683/16000000000000 : ℝ)^2193 := by
      have hnat : (50001640001309685953 : ℕ)^512*16000000000000^2193 ≤ 16000122523683^2193*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001640001309685953 50000000000000000000 16000122523683 16000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16000122523683/16000000000000 : ℝ)) (X := (50001640001309685953/50000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100080525630867021167/100000000000000000000 : ℝ) ≤ (10001879453015683/10000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (100080525630867021167/100000000000000000000 : ℝ)^512 ≤ (10001879453015683/10000000000000000 : ℝ)^2193 := by
      have hnat : (100080525630867021167 : ℕ)^512*10000000000000000^2193 ≤ 10001879453015683^2193*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100080525630867021167 100000000000000000000 10001879453015683 10000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001879453015683/10000000000000000 : ℝ)) (X := (100080525630867021167/100000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25039442814778667607/25000000000000000000 : ℝ) ≤ (10003682328729491/10000000000000000 : ℝ) ^ (2193/512 : ℝ) := by
    have hpowers : (25039442814778667607/25000000000000000000 : ℝ)^512 ≤ (10003682328729491/10000000000000000 : ℝ)^2193 := by
      have hnat : (25039442814778667607 : ℕ)^512*10000000000000000^2193 ≤ 10003682328729491^2193*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25039442814778667607 25000000000000000000 10003682328729491 10000000000000000 512 2193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003682328729491/10000000000000000 : ℝ)) (X := (25039442814778667607/25000000000000000000 : ℝ)) (by norm_num) 2193 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1640001309685953/100000000000000000000 : ℝ) ≤ ((22444665933612739743/22450000000000000000 : ℝ)+2*(112679732113/70156250000000 : ℝ)*(1527/20000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (22444665933612739743/22450000000000000000 : ℝ)+2*(112679732113/70156250000000 : ℝ)*(1527/20000 : ℝ)=(16000122523683/16000000000000 : ℝ) by norm_num, show 1+2*(1640001309685953/100000000000000000000 : ℝ)=(50001640001309685953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39442814778667607/50000000000000000000 : ℝ)+(1640001309685953/100000000000000000000 : ℝ) ≤ ((22444665933612739743/22450000000000000000 : ℝ)+(112679732113/70156250000000 : ℝ)*((943/5000 : ℝ)+(1527/20000 : ℝ)))^(2193/512 : ℝ) := by
    rw [show (22444665933612739743/22450000000000000000 : ℝ)+(112679732113/70156250000000 : ℝ)*((943/5000 : ℝ)+(1527/20000 : ℝ))=(10001879453015683/10000000000000000 : ℝ) by norm_num, show 1+(39442814778667607/50000000000000000000 : ℝ)+(1640001309685953/100000000000000000000 : ℝ)=(100080525630867021167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39442814778667607/50000000000000000000 : ℝ) ≤ ((22444665933612739743/22450000000000000000 : ℝ)+2*(112679732113/70156250000000 : ℝ)*(943/5000 : ℝ))^(2193/512 : ℝ) := by
    rw [show (22444665933612739743/22450000000000000000 : ℝ)+2*(112679732113/70156250000000 : ℝ)*(943/5000 : ℝ)=(10003682328729491/10000000000000000 : ℝ) by norm_num, show 1+2*(39442814778667607/50000000000000000000 : ℝ)=(25039442814778667607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22444665933612739743/22450000000000000000 : ℝ)*(X 1 0+X 2 0)+(112679732113/70156250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (1527/20000 : ℝ)) (hi := (943/5000 : ℝ)) (c := (22444665933612739743/22450000000000000000 : ℝ)) (alpha := (112679732113/70156250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22444665933612739743/22450000000000000000 : ℝ)*(X 0 1+X 2 1)+(112679732113/70156250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (1527/20000 : ℝ)) (hi := (943/5000 : ℝ)) (c := (22444665933612739743/22450000000000000000 : ℝ)) (alpha := (112679732113/70156250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22444665933612739743/22450000000000000000 : ℝ)*(X 0 2+X 1 2)+(112679732113/70156250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2193/512 : ℝ)) (lo := (1527/20000 : ℝ)) (hi := (943/5000 : ℝ)) (c := (22444665933612739743/22450000000000000000 : ℝ)) (alpha := (112679732113/70156250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-982932723/5000000000 : ℝ)*X 0 0+(5458627323/10000000000 : ℝ)*X 0 1+(1300267223/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340067259/2500000000 : ℝ)*X 1 0+(-1049194973/5000000000 : ℝ)*X 1 1+(1300267199/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670033583/1250000000 : ℝ)*X 2 0+(2600534609/5000000000 : ℝ)*X 2 1+(-419677977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((537561303/1250000000 : ℝ)*X 0 0+(2015098727/5000000000 : ℝ)*X 0 1+(4586974277/10000000000 : ℝ)*X 0 2+(537561303/1250000000 : ℝ)*X 1 0+(2015098727/5000000000 : ℝ)*X 1 1+(4586974277/10000000000 : ℝ)*X 1 2+(537561303/1250000000 : ℝ)*X 2 0+(2015098727/5000000000 : ℝ)*X 2 1+(4586974277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-491477857/2500000000 : ℝ)*X 0 0+(162579541/312500000 : ℝ)*X 0 1+(1091427731/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529330787/1000000000 : ℝ)*X 1 0+(-115144991/625000000 : ℝ)*X 1 1+(5457139039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293307791/10000000000 : ℝ)*X 2 0+(1364284753/2500000000 : ℝ)*X 2 1+(-1842320003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300589603/10000000000 : ℝ)*X 0 0+(572972859/1250000000 : ℝ)*X 0 1+(252088451/625000000 : ℝ)*X 0 2+(4300589603/10000000000 : ℝ)*X 1 0+(572972859/1250000000 : ℝ)*X 1 1+(252088451/625000000 : ℝ)*X 1 2+(4300589603/10000000000 : ℝ)*X 2 0+(572972859/1250000000 : ℝ)*X 2 1+(252088451/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1427_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62991057452189893337373/14031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (106157259/25000000000000 : ℝ)*(base19) + (95431599/100000000000000 : ℝ)*(lower2) + (27052481/20000000000000 : ℝ)*(upper3) + (2450493/20000000000000 : ℝ)*(lower4) + (13252269/100000000000000 : ℝ)*(upper5) + (709834311755727/25000000000000 : ℝ)*(major0) + (709834311755727/25000000000000 : ℝ)*(major1) + (709834311755727/25000000000000 : ℝ)*(major2) + (1941309254617409/50000000000000 : ℝ)*(sp0) + (1941309652312417/50000000000000 : ℝ)*(sp1) + (388261972925387/10000000000000 : ℝ)*(sp2) + (449013168651389/25000000000000 : ℝ)*(sp3) + (305004763/25000000000000 : ℝ)*(sp4) + (485135427/25000000000000 : ℝ)*(sp7) + (7015838340419/390625000000 : ℝ)*(f.failure) + (388261972925387/10000000000000 : ℝ)*(f.sum) + (15980315732917/7015625000000000000000000000 : ℝ)*base66 + (201381578031578161/561250000000000000000000000000000 : ℝ)*base67 + (343228716570921839/561250000000000000000000000000000 : ℝ)*base70 + (1919975863025921839/561250000000000000000000000000000 : ℝ)*base72 + (38856093998291/14031250000000000000000000000 : ℝ)*base73 + (1073734941614078161/561250000000000000000000000000000 : ℝ)*base75 + (1349367317544078161/561250000000000000000000000000000 : ℝ)*base77 + (1186790162815921839/561250000000000000000000000000000 : ℝ)*base80 + (107726107200043/28062500000000000000000000000 : ℝ)*base82 + (8827/39062500000000000000 : ℝ)*base90 + (8827/39062500000000000000 : ℝ)*base92 + (8827/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268427262631371082136793/28062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (135776143/12500000000000 : ℝ)*(base19) + (155750483/12500000000000 : ℝ)*(base23) + (49978889/20000000000000 : ℝ)*(upper3) + (6337961/6250000000000 : ℝ)*(lower4) + (36988299/25000000000000 : ℝ)*(upper5) + (2872398038021663/100000000000000 : ℝ)*(major0) + (2872398038021663/100000000000000 : ℝ)*(major1) + (2872398038021663/100000000000000 : ℝ)*(major2) + (1925174239/12500000000000 : ℝ)*(sp1) + (3504621293/20000000000000 : ℝ)*(sp2) + (1963914083985333/50000000000000 : ℝ)*(sp4) + (392781168036761/10000000000000 : ℝ)*(sp5) + (1963904699430169/50000000000000 : ℝ)*(sp6) + (1816967589228097/100000000000000 : ℝ)*(sp7) + (1816967589228097/100000000000000 : ℝ)*(f.failure) + (1963914083985333/50000000000000 : ℝ)*(f.sum) + (379354894640671/56125000000000000000000000000 : ℝ)*base66 + (131843537349132609/2245000000000000000000000000000000 : ℝ)*base67 + (9162028702879132609/2245000000000000000000000000000000 : ℝ)*base69 + (10151833905165867391/2245000000000000000000000000000000 : ℝ)*base72 + (27955052077287/7015625000000000000000000000 : ℝ)*base74 + (7646648063439132609/2245000000000000000000000000000000 : ℝ)*base75 + (13952633690735867391/2245000000000000000000000000000000 : ℝ)*base78 + (1519988475980867391/2245000000000000000000000000000000 : ℝ)*base80 + (110189046456921/56125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (39960299/10000000000000000000000 : ℝ)*base89 + (39960299/10000000000000000000000 : ℝ)*base91 + (39960299/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1427_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (943/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1527/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1427_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1427_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1427_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1427_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1427_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2193/512 : ℝ) ≤ p) (hpb : p ≤ (4387/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158087467/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1427_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
