-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1548_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:26.187241+00:00
-- url     : https://prove2.me/submissions/e05e7a6d-1c7b-4e8e-919b-794007a13036

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
theorem support_rectangle_w1548_s3_0 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1815790857/10000000000 : ℝ)*x 0 + (1086150541/2000000000 : ℝ)*x 1 + (5217307889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1815790857/10000000000 : ℝ)^4593 ≤ (1112962727697/10000000000000 : ℝ)^3569 := by
    have hnat : (1815790857 : ℕ)^4593*10000000000000^3569 ≤ 1112962727697^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815790857 10000000000 1112962727697 10000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086150541/2000000000 : ℝ)^4593 ≤ (911627380099/2000000000000 : ℝ)^3569 := by
    have hnat : (1086150541 : ℕ)^4593*2000000000000^3569 ≤ 911627380099^3569*2000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086150541 2000000000 911627380099 2000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217307889/10000000000 : ℝ)^4593 ≤ (10822250923357/25000000000000 : ℝ)^3569 := by
    have hnat : (5217307889 : ℕ)^4593*25000000000000^3569 ≤ 10822250923357^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217307889 10000000000 10822250923357 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1815790857/10000000000 : ℝ), (1086150541/2000000000 : ℝ), (5217307889/10000000000 : ℝ)] ![(1112962727697/10000000000000 : ℝ), (911627380099/2000000000000 : ℝ), (10822250923357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1815790857/10000000000 : ℝ)|^4593 ≤ (1112962727697/10000000000000 : ℝ)^3569
        have hw : |(-1815790857/10000000000 : ℝ)|=(1815790857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086150541/2000000000 : ℝ)|^4593 ≤ (911627380099/2000000000000 : ℝ)^3569
        have hw : |(1086150541/2000000000 : ℝ)|=(1086150541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217307889/10000000000 : ℝ)|^4593 ≤ (10822250923357/25000000000000 : ℝ)^3569
        have hw : |(5217307889/10000000000 : ℝ)|=(5217307889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s3_1 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350089731/10000000000 : ℝ)*x 0 + (-1925079583/10000000000 : ℝ)*x 1 + (5217307857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350089731/10000000000 : ℝ)^4593 ≤ (44711964674591/100000000000000 : ℝ)^3569 := by
    have hnat : (5350089731 : ℕ)^4593*100000000000000^3569 ≤ 44711964674591^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350089731 10000000000 44711964674591 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1925079583/10000000000 : ℝ)^4593 ≤ (11999031960991/100000000000000 : ℝ)^3569 := by
    have hnat : (1925079583 : ℕ)^4593*100000000000000^3569 ≤ 11999031960991^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925079583 10000000000 11999031960991 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217307857/10000000000 : ℝ)^4593 ≤ (43289003351739/100000000000000 : ℝ)^3569 := by
    have hnat : (5217307857 : ℕ)^4593*100000000000000^3569 ≤ 43289003351739^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217307857 10000000000 43289003351739 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350089731/10000000000 : ℝ), (-1925079583/10000000000 : ℝ), (5217307857/10000000000 : ℝ)] ![(44711964674591/100000000000000 : ℝ), (11999031960991/100000000000000 : ℝ), (43289003351739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350089731/10000000000 : ℝ)|^4593 ≤ (44711964674591/100000000000000 : ℝ)^3569
        have hw : |(5350089731/10000000000 : ℝ)|=(5350089731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1925079583/10000000000 : ℝ)|^4593 ≤ (11999031960991/100000000000000 : ℝ)^3569
        have hw : |(-1925079583/10000000000 : ℝ)|=(1925079583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217307857/10000000000 : ℝ)|^4593 ≤ (43289003351739/100000000000000 : ℝ)^3569
        have hw : |(5217307857/10000000000 : ℝ)|=(5217307857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s3_2 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350089757/10000000000 : ℝ)*x 0 + (5217307841/10000000000 : ℝ)*x 1 + (-1925079569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350089757/10000000000 : ℝ)^4593 ≤ (22355982477111/50000000000000 : ℝ)^3569 := by
    have hnat : (5350089757 : ℕ)^4593*50000000000000^3569 ≤ 22355982477111^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350089757 10000000000 22355982477111 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217307841/10000000000 : ℝ)^4593 ≤ (21644501590447/50000000000000 : ℝ)^3569 := by
    have hnat : (5217307841 : ℕ)^4593*50000000000000^3569 ≤ 21644501590447^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217307841 10000000000 21644501590447 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925079569/10000000000 : ℝ)^4593 ≤ (2999757962173/25000000000000 : ℝ)^3569 := by
    have hnat : (1925079569 : ℕ)^4593*25000000000000^3569 ≤ 2999757962173^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925079569 10000000000 2999757962173 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350089757/10000000000 : ℝ), (5217307841/10000000000 : ℝ), (-1925079569/10000000000 : ℝ)] ![(22355982477111/50000000000000 : ℝ), (21644501590447/50000000000000 : ℝ), (2999757962173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350089757/10000000000 : ℝ)|^4593 ≤ (22355982477111/50000000000000 : ℝ)^3569
        have hw : |(5350089757/10000000000 : ℝ)|=(5350089757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217307841/10000000000 : ℝ)|^4593 ≤ (21644501590447/50000000000000 : ℝ)^3569
        have hw : |(5217307841/10000000000 : ℝ)|=(5217307841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1925079569/10000000000 : ℝ)|^4593 ≤ (2999757962173/25000000000000 : ℝ)^3569
        have hw : |(-1925079569/10000000000 : ℝ)|=(1925079569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s3_3 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1063273037/2500000000 : ℝ)*x 0 + (2005452861/5000000000 : ℝ)*x 1 + (4507213049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063273037/2500000000 : ℝ)^4593 ≤ (332793311937/1000000000000 : ℝ)^3569 := by
    have hnat : (1063273037 : ℕ)^4593*1000000000000^3569 ≤ 332793311937^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063273037 2500000000 332793311937 1000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005452861/5000000000 : ℝ)^4593 ≤ (964398982669/3125000000000 : ℝ)^3569 := by
    have hnat : (2005452861 : ℕ)^4593*3125000000000^3569 ≤ 964398982669^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005452861 5000000000 964398982669 3125000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507213049/10000000000 : ℝ)^4593 ≤ (7171980267979/20000000000000 : ℝ)^3569 := by
    have hnat : (4507213049 : ℕ)^4593*20000000000000^3569 ≤ 7171980267979^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507213049 10000000000 7171980267979 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063273037/2500000000 : ℝ), (2005452861/5000000000 : ℝ), (4507213049/10000000000 : ℝ)] ![(332793311937/1000000000000 : ℝ), (964398982669/3125000000000 : ℝ), (7171980267979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063273037/2500000000 : ℝ)|^4593 ≤ (332793311937/1000000000000 : ℝ)^3569
        have hw : |(1063273037/2500000000 : ℝ)|=(1063273037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2005452861/5000000000 : ℝ)|^4593 ≤ (964398982669/3125000000000 : ℝ)^3569
        have hw : |(2005452861/5000000000 : ℝ)|=(2005452861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507213049/10000000000 : ℝ)|^4593 ≤ (7171980267979/20000000000000 : ℝ)^3569
        have hw : |(4507213049/10000000000 : ℝ)|=(4507213049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s3_4 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1815820081/10000000000 : ℝ)*x 0 + (5218436139/10000000000 : ℝ)*x 1 + (108592319/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1815820081/10000000000 : ℝ)^4593 ≤ (5564928897621/50000000000000 : ℝ)^3569 := by
    have hnat : (1815820081 : ℕ)^4593*50000000000000^3569 ≤ 5564928897621^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815820081 10000000000 5564928897621 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218436139/10000000000 : ℝ)^4593 ≤ (433010512739/1000000000000 : ℝ)^3569 := by
    have hnat : (5218436139 : ℕ)^4593*1000000000000^3569 ≤ 433010512739^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218436139 10000000000 433010512739 1000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108592319/200000000 : ℝ)^4593 ≤ (45569090907777/100000000000000 : ℝ)^3569 := by
    have hnat : (108592319 : ℕ)^4593*100000000000000^3569 ≤ 45569090907777^3569*200000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108592319 200000000 45569090907777 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1815820081/10000000000 : ℝ), (5218436139/10000000000 : ℝ), (108592319/200000000 : ℝ)] ![(5564928897621/50000000000000 : ℝ), (433010512739/1000000000000 : ℝ), (45569090907777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1815820081/10000000000 : ℝ)|^4593 ≤ (5564928897621/50000000000000 : ℝ)^3569
        have hw : |(-1815820081/10000000000 : ℝ)|=(1815820081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218436139/10000000000 : ℝ)|^4593 ≤ (433010512739/1000000000000 : ℝ)^3569
        have hw : |(5218436139/10000000000 : ℝ)|=(5218436139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108592319/200000000 : ℝ)|^4593 ≤ (45569090907777/100000000000000 : ℝ)^3569
        have hw : |(108592319/200000000 : ℝ)|=(108592319/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s3_5 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293772697/10000000000 : ℝ)*x 0 + (-171277149/1000000000 : ℝ)*x 1 + (2714807983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293772697/10000000000 : ℝ)^4593 ≤ (5513398611893/12500000000000 : ℝ)^3569 := by
    have hnat : (5293772697 : ℕ)^4593*12500000000000^3569 ≤ 5513398611893^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293772697 10000000000 5513398611893 12500000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171277149/1000000000 : ℝ)^4593 ≤ (10323720010073/100000000000000 : ℝ)^3569 := by
    have hnat : (171277149 : ℕ)^4593*100000000000000^3569 ≤ 10323720010073^3569*1000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171277149 1000000000 10323720010073 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714807983/5000000000 : ℝ)^4593 ≤ (11392272770147/25000000000000 : ℝ)^3569 := by
    have hnat : (2714807983 : ℕ)^4593*25000000000000^3569 ≤ 11392272770147^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714807983 5000000000 11392272770147 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293772697/10000000000 : ℝ), (-171277149/1000000000 : ℝ), (2714807983/5000000000 : ℝ)] ![(5513398611893/12500000000000 : ℝ), (10323720010073/100000000000000 : ℝ), (11392272770147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293772697/10000000000 : ℝ)|^4593 ≤ (5513398611893/12500000000000 : ℝ)^3569
        have hw : |(5293772697/10000000000 : ℝ)|=(5293772697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171277149/1000000000 : ℝ)|^4593 ≤ (10323720010073/100000000000000 : ℝ)^3569
        have hw : |(-171277149/1000000000 : ℝ)|=(171277149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714807983/5000000000 : ℝ)|^4593 ≤ (11392272770147/25000000000000 : ℝ)^3569
        have hw : |(2714807983/5000000000 : ℝ)|=(2714807983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s3_6 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293772693/10000000000 : ℝ)*x 0 + (2714807983/5000000000 : ℝ)*x 1 + (-214096437/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293772693/10000000000 : ℝ)^4593 ≤ (22053594426127/50000000000000 : ℝ)^3569 := by
    have hnat : (5293772693 : ℕ)^4593*50000000000000^3569 ≤ 22053594426127^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293772693 10000000000 22053594426127 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714807983/5000000000 : ℝ)^4593 ≤ (11392272770147/25000000000000 : ℝ)^3569 := by
    have hnat : (2714807983 : ℕ)^4593*25000000000000^3569 ≤ 11392272770147^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714807983 5000000000 11392272770147 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214096437/1250000000 : ℝ)^4593 ≤ (5161860028307/50000000000000 : ℝ)^3569 := by
    have hnat : (214096437 : ℕ)^4593*50000000000000^3569 ≤ 5161860028307^3569*1250000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214096437 1250000000 5161860028307 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293772693/10000000000 : ℝ), (2714807983/5000000000 : ℝ), (-214096437/1250000000 : ℝ)] ![(22053594426127/50000000000000 : ℝ), (11392272770147/25000000000000 : ℝ), (5161860028307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293772693/10000000000 : ℝ)|^4593 ≤ (22053594426127/50000000000000 : ℝ)^3569
        have hw : |(5293772693/10000000000 : ℝ)|=(5293772693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714807983/5000000000 : ℝ)|^4593 ≤ (11392272770147/25000000000000 : ℝ)^3569
        have hw : |(2714807983/5000000000 : ℝ)|=(2714807983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214096437/1250000000 : ℝ)|^4593 ≤ (5161860028307/50000000000000 : ℝ)^3569
        have hw : |(-214096437/1250000000 : ℝ)|=(214096437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s3_7 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1063290017/2500000000 : ℝ)*x 0 + (2252294801/5000000000 : ℝ)*x 1 + (4013548919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063290017/2500000000 : ℝ)^4593 ≤ (33280015134271/100000000000000 : ℝ)^3569 := by
    have hnat : (1063290017 : ℕ)^4593*100000000000000^3569 ≤ 33280015134271^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063290017 2500000000 33280015134271 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252294801/5000000000 : ℝ)^4593 ≤ (1119782578753/3125000000000 : ℝ)^3569 := by
    have hnat : (2252294801 : ℕ)^4593*3125000000000^3569 ≤ 1119782578753^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252294801 5000000000 1119782578753 3125000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4013548919/10000000000 : ℝ)^4593 ≤ (15443471164159/50000000000000 : ℝ)^3569 := by
    have hnat : (4013548919 : ℕ)^4593*50000000000000^3569 ≤ 15443471164159^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013548919 10000000000 15443471164159 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063290017/2500000000 : ℝ), (2252294801/5000000000 : ℝ), (4013548919/10000000000 : ℝ)] ![(33280015134271/100000000000000 : ℝ), (1119782578753/3125000000000 : ℝ), (15443471164159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063290017/2500000000 : ℝ)|^4593 ≤ (33280015134271/100000000000000 : ℝ)^3569
        have hw : |(1063290017/2500000000 : ℝ)|=(1063290017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252294801/5000000000 : ℝ)|^4593 ≤ (1119782578753/3125000000000 : ℝ)^3569
        have hw : |(2252294801/5000000000 : ℝ)|=(2252294801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4013548919/10000000000 : ℝ)|^4593 ≤ (15443471164159/50000000000000 : ℝ)^3569
        have hw : |(4013548919/10000000000 : ℝ)|=(4013548919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1548_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10689/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5503/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1553/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7937/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10689/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7937/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10689/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7937/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10689/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7937/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10689/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7937/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10689/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7937/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10689/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10689/100000 : ℝ) ^ (4591/1024 : ℝ) ≤ (1107332425377217/25000000000000000000 : ℝ) := by
    have hpowers : (10689/100000 : ℝ)^4591 ≤ (1107332425377217/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10689 : ℕ)^4591*25000000000000000000^1024 ≤ 1107332425377217^1024*100000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10689 100000 1107332425377217 25000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10689/100000 : ℝ)) (X := (1107332425377217/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7937/50000 : ℝ) ^ (4591/1024 : ℝ) ≤ (13041530196628561/50000000000000000000 : ℝ) := by
    have hpowers : (7937/50000 : ℝ)^4591 ≤ (13041530196628561/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7937 : ℕ)^4591*50000000000000000000^1024 ≤ 13041530196628561^1024*50000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7937 50000 13041530196628561 50000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7937/50000 : ℝ)) (X := (13041530196628561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501107332425377217/12500000000000000000 : ℝ) ≤ (2000039516249477/2000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (12501107332425377217/12500000000000000000 : ℝ)^1024 ≤ (2000039516249477/2000000000000000 : ℝ)^4591 := by
      have hnat : (12501107332425377217 : ℕ)^1024*2000000000000000^4591 ≤ 2000039516249477^4591*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501107332425377217 12500000000000000000 2000039516249477 2000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000039516249477/2000000000000000 : ℝ)) (X := (12501107332425377217/12500000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003051239009476599/10000000000000000000 : ℝ) ≤ (10000680483218821/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (10003051239009476599/10000000000000000000 : ℝ)^1024 ≤ (10000680483218821/10000000000000000 : ℝ)^4591 := by
      have hnat : (10003051239009476599 : ℕ)^1024*10000000000000000^4591 ≤ 10000680483218821^4591*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003051239009476599 10000000000000000000 10000680483218821 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000680483218821/10000000000000000 : ℝ)) (X := (10003051239009476599/10000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013041530196628561/25000000000000000000 : ℝ) ≤ (10001163385190257/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (25013041530196628561/25000000000000000000 : ℝ)^1024 ≤ (10001163385190257/10000000000000000 : ℝ)^4591 := by
      have hnat : (25013041530196628561 : ℕ)^1024*10000000000000000^4591 ≤ 10001163385190257^4591*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013041530196628561 25000000000000000000 10001163385190257 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001163385190257/10000000000000000 : ℝ)) (X := (25013041530196628561/25000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1107332425377217/25000000000000000000 : ℝ) ≤ ((51840700980422332417/51850000000000000000 : ℝ)+2*(120725492859/129625000000000 : ℝ)*(10689/100000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (51840700980422332417/51850000000000000000 : ℝ)+2*(120725492859/129625000000000 : ℝ)*(10689/100000 : ℝ)=(2000039516249477/2000000000000000 : ℝ) by norm_num, show 1+2*(1107332425377217/25000000000000000000 : ℝ)=(12501107332425377217/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13041530196628561/50000000000000000000 : ℝ)+(1107332425377217/25000000000000000000 : ℝ) ≤ ((51840700980422332417/51850000000000000000 : ℝ)+(120725492859/129625000000000 : ℝ)*((7937/50000 : ℝ)+(10689/100000 : ℝ)))^(4591/1024 : ℝ) := by
    rw [show (51840700980422332417/51850000000000000000 : ℝ)+(120725492859/129625000000000 : ℝ)*((7937/50000 : ℝ)+(10689/100000 : ℝ))=(10000680483218821/10000000000000000 : ℝ) by norm_num, show 1+(13041530196628561/50000000000000000000 : ℝ)+(1107332425377217/25000000000000000000 : ℝ)=(10003051239009476599/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13041530196628561/50000000000000000000 : ℝ) ≤ ((51840700980422332417/51850000000000000000 : ℝ)+2*(120725492859/129625000000000 : ℝ)*(7937/50000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (51840700980422332417/51850000000000000000 : ℝ)+2*(120725492859/129625000000000 : ℝ)*(7937/50000 : ℝ)=(10001163385190257/10000000000000000 : ℝ) by norm_num, show 1+2*(13041530196628561/50000000000000000000 : ℝ)=(25013041530196628561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (51840700980422332417/51850000000000000000 : ℝ)*(X 1 0+X 2 0)+(120725492859/129625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (10689/100000 : ℝ)) (hi := (7937/50000 : ℝ)) (c := (51840700980422332417/51850000000000000000 : ℝ)) (alpha := (120725492859/129625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (51840700980422332417/51850000000000000000 : ℝ)*(X 0 1+X 2 1)+(120725492859/129625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (10689/100000 : ℝ)) (hi := (7937/50000 : ℝ)) (c := (51840700980422332417/51850000000000000000 : ℝ)) (alpha := (120725492859/129625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (51840700980422332417/51850000000000000000 : ℝ)*(X 0 2+X 1 2)+(120725492859/129625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (10689/100000 : ℝ)) (hi := (7937/50000 : ℝ)) (c := (51840700980422332417/51850000000000000000 : ℝ)) (alpha := (120725492859/129625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1815790857/10000000000 : ℝ)*X 0 0+(1086150541/2000000000 : ℝ)*X 0 1+(5217307889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350089731/10000000000 : ℝ)*X 1 0+(-1925079583/10000000000 : ℝ)*X 1 1+(5217307857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350089757/10000000000 : ℝ)*X 2 0+(5217307841/10000000000 : ℝ)*X 2 1+(-1925079569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1063273037/2500000000 : ℝ)*X 0 0+(2005452861/5000000000 : ℝ)*X 0 1+(4507213049/10000000000 : ℝ)*X 0 2+(1063273037/2500000000 : ℝ)*X 1 0+(2005452861/5000000000 : ℝ)*X 1 1+(4507213049/10000000000 : ℝ)*X 1 2+(1063273037/2500000000 : ℝ)*X 2 0+(2005452861/5000000000 : ℝ)*X 2 1+(4507213049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1815820081/10000000000 : ℝ)*X 0 0+(5218436139/10000000000 : ℝ)*X 0 1+(108592319/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293772697/10000000000 : ℝ)*X 1 0+(-171277149/1000000000 : ℝ)*X 1 1+(2714807983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293772693/10000000000 : ℝ)*X 2 0+(2714807983/5000000000 : ℝ)*X 2 1+(-214096437/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1063290017/2500000000 : ℝ)*X 0 0+(2252294801/5000000000 : ℝ)*X 0 1+(4013548919/10000000000 : ℝ)*X 0 2+(1063290017/2500000000 : ℝ)*X 1 0+(2252294801/5000000000 : ℝ)*X 1 1+(4013548919/10000000000 : ℝ)*X 1 2+(1063290017/2500000000 : ℝ)*X 2 0+(2252294801/5000000000 : ℝ)*X 2 1+(4013548919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8507693393687793828420547749/1296250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232075327/20000000000000 : ℝ)*(base19) + (558570511/50000000000000 : ℝ)*(base23) + (17656333/50000000000000 : ℝ)*(lower2) + (38148907/25000000000000 : ℝ)*(upper3) + (12149477/10000000000000 : ℝ)*(upper5) + (1674996216555001/50000000000000 : ℝ)*(major0) + (1674996216555001/50000000000000 : ℝ)*(major1) + (1674996216555001/50000000000000 : ℝ)*(major2) + (4685069898925261/100000000000000 : ℝ)*(sp0) + (4685086984888807/100000000000000 : ℝ)*(sp1) + (4685087028124421/100000000000000 : ℝ)*(sp2) + (1007444103338873/50000000000000 : ℝ)*(sp3) + (9123170091/50000000000000 : ℝ)*(sp4) + (4147749869/50000000000000 : ℝ)*(sp7) + (503724125544371/25000000000000 : ℝ)*(f.failure) + (4685088145265443/100000000000000 : ℝ)*(f.sum) + (95225141557153/25925000000000000000000000000 : ℝ)*base66 + (5614739046461867417/2592500000000000000000000000000000 : ℝ)*base67 + (584841803916867417/2592500000000000000000000000000000 : ℝ)*base69 + (3237063142046867417/2592500000000000000000000000000000 : ℝ)*base71 + (74147915223603/25925000000000000000000000000 : ℝ)*base74 + (12073479315558132583/2592500000000000000000000000000000 : ℝ)*base76 + (41369789425103132583/2592500000000000000000000000000000 : ℝ)*base78 + (2499417976346867417/2592500000000000000000000000000000 : ℝ)*base79 + (51273686782103/25925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5816843/1250000000000000000000 : ℝ)*base89 + (5816843/1250000000000000000000 : ℝ)*base91 + (5816843/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5001540215271849040547026473/648125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1252449389/100000000000000 : ℝ)*(base19) + (83014549/6250000000000 : ℝ)*(base23) + (168682411/100000000000000 : ℝ)*(upper3) + (35650423/100000000000000 : ℝ)*(lower4) + (160360211/100000000000000 : ℝ)*(upper5) + (846473940835277/25000000000000 : ℝ)*(major0) + (846473940835277/25000000000000 : ℝ)*(major1) + (846473940835277/25000000000000 : ℝ)*(major2) + (9686665749/50000000000000 : ℝ)*(sp1) + (1025147199/5000000000000 : ℝ)*(sp2) + (1183825060631609/25000000000000 : ℝ)*(sp4) + (4735279616745549/100000000000000 : ℝ)*(sp5) + (4735278411349671/100000000000000 : ℝ)*(sp6) + (50912275673113/2500000000000 : ℝ)*(sp7) + (50912275673113/2500000000000 : ℝ)*(f.failure) + (1183825060631609/25000000000000 : ℝ)*(f.sum) + (14900169100097/6481250000000000000000000000 : ℝ)*base65 + (3108095483776474509/1296250000000000000000000000000000 : ℝ)*base67 + (7448671003611474509/1296250000000000000000000000000000 : ℝ)*base69 + (1266800348702724509/1296250000000000000000000000000000 : ℝ)*base71 + (846181770143/1620312500000000000000000000 : ℝ)*base73 + (4721251088938525491/1296250000000000000000000000000000 : ℝ)*base76 + (490945984252275491/1296250000000000000000000000000000 : ℝ)*base78 + (14226130557283974509/1296250000000000000000000000000000 : ℝ)*base79 + (22279944601347/6481250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (229471/125000000000000000000 : ℝ)*base90 + (229471/125000000000000000000 : ℝ)*base92 + (229471/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1548_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10689/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1553/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1548_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1548_s4_0 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1816080957/10000000000 : ℝ)*x 0 + (1357205069/2500000000 : ℝ)*x 1 + (1043809637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1816080957/10000000000 : ℝ)^4593 ≤ (445276625063/4000000000000 : ℝ)^3569 := by
    have hnat : (1816080957 : ℕ)^4593*4000000000000^3569 ≤ 445276625063^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816080957 10000000000 445276625063 4000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357205069/2500000000 : ℝ)^4593 ≤ (22780248633591/50000000000000 : ℝ)^3569 := by
    have hnat : (1357205069 : ℕ)^4593*50000000000000^3569 ≤ 22780248633591^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357205069 2500000000 22780248633591 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043809637/2000000000 : ℝ)^4593 ≤ (43307587082653/100000000000000 : ℝ)^3569 := by
    have hnat : (1043809637 : ℕ)^4593*100000000000000^3569 ≤ 43307587082653^3569*2000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043809637 2000000000 43307587082653 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1816080957/10000000000 : ℝ), (1357205069/2500000000 : ℝ), (1043809637/2000000000 : ℝ)] ![(445276625063/4000000000000 : ℝ), (22780248633591/50000000000000 : ℝ), (43307587082653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1816080957/10000000000 : ℝ)|^4593 ≤ (445276625063/4000000000000 : ℝ)^3569
        have hw : |(-1816080957/10000000000 : ℝ)|=(1816080957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357205069/2500000000 : ℝ)|^4593 ≤ (22780248633591/50000000000000 : ℝ)^3569
        have hw : |(1357205069/2500000000 : ℝ)|=(1357205069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043809637/2000000000 : ℝ)|^4593 ≤ (43307587082653/100000000000000 : ℝ)^3569
        have hw : |(1043809637/2000000000 : ℝ)|=(1043809637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s4_1 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349580141/10000000000 : ℝ)*x 0 + (-961723211/5000000000 : ℝ)*x 1 + (1304761939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349580141/10000000000 : ℝ)^4593 ≤ (11176621020411/25000000000000 : ℝ)^3569 := by
    have hnat : (5349580141 : ℕ)^4593*25000000000000^3569 ≤ 11176621020411^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349580141 10000000000 11176621020411 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961723211/5000000000 : ℝ)^4593 ≤ (11985933401079/100000000000000 : ℝ)^3569 := by
    have hnat : (961723211 : ℕ)^4593*100000000000000^3569 ≤ 11985933401079^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961723211 5000000000 11985933401079 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304761939/2500000000 : ℝ)^4593 ≤ (21653791250723/50000000000000 : ℝ)^3569 := by
    have hnat : (1304761939 : ℕ)^4593*50000000000000^3569 ≤ 21653791250723^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304761939 2500000000 21653791250723 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349580141/10000000000 : ℝ), (-961723211/5000000000 : ℝ), (1304761939/2500000000 : ℝ)] ![(11176621020411/25000000000000 : ℝ), (11985933401079/100000000000000 : ℝ), (21653791250723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349580141/10000000000 : ℝ)|^4593 ≤ (11176621020411/25000000000000 : ℝ)^3569
        have hw : |(5349580141/10000000000 : ℝ)|=(5349580141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-961723211/5000000000 : ℝ)|^4593 ≤ (11985933401079/100000000000000 : ℝ)^3569
        have hw : |(-961723211/5000000000 : ℝ)|=(961723211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304761939/2500000000 : ℝ)|^4593 ≤ (21653791250723/50000000000000 : ℝ)^3569
        have hw : |(1304761939/2500000000 : ℝ)|=(1304761939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s4_2 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349580337/10000000000 : ℝ)*x 0 + (5219047867/10000000000 : ℝ)*x 1 + (-1923446011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349580337/10000000000 : ℝ)^4593 ≤ (44706486189577/100000000000000 : ℝ)^3569 := by
    have hnat : (5349580337 : ℕ)^4593*100000000000000^3569 ≤ 44706486189577^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349580337 10000000000 44706486189577 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219047867/10000000000 : ℝ)^4593 ≤ (43307583686793/100000000000000 : ℝ)^3569 := by
    have hnat : (5219047867 : ℕ)^4593*100000000000000^3569 ≤ 43307583686793^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219047867 10000000000 43307583686793 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923446011/10000000000 : ℝ)^4593 ≤ (11985930105107/100000000000000 : ℝ)^3569 := by
    have hnat : (1923446011 : ℕ)^4593*100000000000000^3569 ≤ 11985930105107^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923446011 10000000000 11985930105107 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349580337/10000000000 : ℝ), (5219047867/10000000000 : ℝ), (-1923446011/10000000000 : ℝ)] ![(44706486189577/100000000000000 : ℝ), (43307583686793/100000000000000 : ℝ), (11985930105107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349580337/10000000000 : ℝ)|^4593 ≤ (44706486189577/100000000000000 : ℝ)^3569
        have hw : |(5349580337/10000000000 : ℝ)|=(5349580337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219047867/10000000000 : ℝ)|^4593 ≤ (43307583686793/100000000000000 : ℝ)^3569
        have hw : |(5219047867/10000000000 : ℝ)|=(5219047867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1923446011/10000000000 : ℝ)|^4593 ≤ (11985930105107/100000000000000 : ℝ)^3569
        have hw : |(-1923446011/10000000000 : ℝ)|=(1923446011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s4_3 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132914841/312500000 : ℝ)*x 0 + (4015155011/10000000000 : ℝ)*x 1 + (4502922681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132914841/312500000 : ℝ)^4593 ≤ (33281171597099/100000000000000 : ℝ)^3569 := by
    have hnat : (132914841 : ℕ)^4593*100000000000000^3569 ≤ 33281171597099^3569*312500000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132914841 312500000 33281171597099 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015155011/10000000000 : ℝ)^4593 ≤ (3862856181241/12500000000000 : ℝ)^3569 := by
    have hnat : (4015155011 : ℕ)^4593*12500000000000^3569 ≤ 3862856181241^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015155011 10000000000 3862856181241 12500000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502922681/10000000000 : ℝ)^4593 ≤ (35815978933827/100000000000000 : ℝ)^3569 := by
    have hnat : (4502922681 : ℕ)^4593*100000000000000^3569 ≤ 35815978933827^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502922681 10000000000 35815978933827 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132914841/312500000 : ℝ), (4015155011/10000000000 : ℝ), (4502922681/10000000000 : ℝ)] ![(33281171597099/100000000000000 : ℝ), (3862856181241/12500000000000 : ℝ), (35815978933827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132914841/312500000 : ℝ)|^4593 ≤ (33281171597099/100000000000000 : ℝ)^3569
        have hw : |(132914841/312500000 : ℝ)|=(132914841/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015155011/10000000000 : ℝ)|^4593 ≤ (3862856181241/12500000000000 : ℝ)^3569
        have hw : |(4015155011/10000000000 : ℝ)|=(4015155011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502922681/10000000000 : ℝ)|^4593 ≤ (35815978933827/100000000000000 : ℝ)^3569
        have hw : |(4502922681/10000000000 : ℝ)|=(4502922681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s4_4 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1816108547/10000000000 : ℝ)*x 0 + (5220137769/10000000000 : ℝ)*x 1 + (5427722727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1816108547/10000000000 : ℝ)^4593 ≤ (5566066632919/50000000000000 : ℝ)^3569 := by
    have hnat : (1816108547 : ℕ)^4593*50000000000000^3569 ≤ 5566066632919^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816108547 10000000000 5566066632919 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220137769/10000000000 : ℝ)^4593 ≤ (8663844576819/20000000000000 : ℝ)^3569 := by
    have hnat : (5220137769 : ℕ)^4593*20000000000000^3569 ≤ 8663844576819^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220137769 10000000000 8663844576819 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427722727/10000000000 : ℝ)^4593 ≤ (711697559883/1562500000000 : ℝ)^3569 := by
    have hnat : (5427722727 : ℕ)^4593*1562500000000^3569 ≤ 711697559883^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427722727 10000000000 711697559883 1562500000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1816108547/10000000000 : ℝ), (5220137769/10000000000 : ℝ), (5427722727/10000000000 : ℝ)] ![(5566066632919/50000000000000 : ℝ), (8663844576819/20000000000000 : ℝ), (711697559883/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1816108547/10000000000 : ℝ)|^4593 ≤ (5566066632919/50000000000000 : ℝ)^3569
        have hw : |(-1816108547/10000000000 : ℝ)|=(1816108547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220137769/10000000000 : ℝ)|^4593 ≤ (8663844576819/20000000000000 : ℝ)^3569
        have hw : |(5220137769/10000000000 : ℝ)|=(5220137769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427722727/10000000000 : ℝ)|^4593 ≤ (711697559883/1562500000000 : ℝ)^3569
        have hw : |(5427722727/10000000000 : ℝ)|=(5427722727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s4_5 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647116277/5000000000 : ℝ)*x 0 + (-1714771457/10000000000 : ℝ)*x 1 + (1356930689/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647116277/5000000000 : ℝ)^4593 ≤ (44112119749797/100000000000000 : ℝ)^3569 := by
    have hnat : (2647116277 : ℕ)^4593*100000000000000^3569 ≤ 44112119749797^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647116277 5000000000 44112119749797 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714771457/10000000000 : ℝ)^4593 ≤ (2584809024597/25000000000000 : ℝ)^3569 := by
    have hnat : (1714771457 : ℕ)^4593*25000000000000^3569 ≤ 2584809024597^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714771457 10000000000 2584809024597 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356930689/2500000000 : ℝ)^4593 ≤ (455486441457/1000000000000 : ℝ)^3569 := by
    have hnat : (1356930689 : ℕ)^4593*1000000000000^3569 ≤ 455486441457^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356930689 2500000000 455486441457 1000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647116277/5000000000 : ℝ), (-1714771457/10000000000 : ℝ), (1356930689/2500000000 : ℝ)] ![(44112119749797/100000000000000 : ℝ), (2584809024597/25000000000000 : ℝ), (455486441457/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647116277/5000000000 : ℝ)|^4593 ≤ (44112119749797/100000000000000 : ℝ)^3569
        have hw : |(2647116277/5000000000 : ℝ)|=(2647116277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1714771457/10000000000 : ℝ)|^4593 ≤ (2584809024597/25000000000000 : ℝ)^3569
        have hw : |(-1714771457/10000000000 : ℝ)|=(1714771457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356930689/2500000000 : ℝ)|^4593 ≤ (455486441457/1000000000000 : ℝ)^3569
        have hw : |(1356930689/2500000000 : ℝ)|=(1356930689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s4_6 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294232337/10000000000 : ℝ)*x 0 + (5427722827/10000000000 : ℝ)*x 1 + (-1714771657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294232337/10000000000 : ℝ)^4593 ≤ (44112117422967/100000000000000 : ℝ)^3569 := by
    have hnat : (5294232337 : ℕ)^4593*100000000000000^3569 ≤ 44112117422967^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294232337 10000000000 44112117422967 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427722827/10000000000 : ℝ)^4593 ≤ (5693580614059/12500000000000 : ℝ)^3569 := by
    have hnat : (5427722827 : ℕ)^4593*12500000000000^3569 ≤ 5693580614059^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427722827 10000000000 5693580614059 12500000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1714771657/10000000000 : ℝ)^4593 ≤ (5169618825141/50000000000000 : ℝ)^3569 := by
    have hnat : (1714771657 : ℕ)^4593*50000000000000^3569 ≤ 5169618825141^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714771657 10000000000 5169618825141 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294232337/10000000000 : ℝ), (5427722827/10000000000 : ℝ), (-1714771657/10000000000 : ℝ)] ![(44112117422967/100000000000000 : ℝ), (5693580614059/12500000000000 : ℝ), (5169618825141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294232337/10000000000 : ℝ)|^4593 ≤ (44112117422967/100000000000000 : ℝ)^3569
        have hw : |(5294232337/10000000000 : ℝ)|=(5294232337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427722827/10000000000 : ℝ)|^4593 ≤ (5693580614059/12500000000000 : ℝ)^3569
        have hw : |(5427722827/10000000000 : ℝ)|=(5427722827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1714771657/10000000000 : ℝ)|^4593 ≤ (5169618825141/50000000000000 : ℝ)^3569
        have hw : |(-1714771657/10000000000 : ℝ)|=(1714771657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s4_7 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253339361/10000000000 : ℝ)*x 0 + (4500388653/10000000000 : ℝ)*x 1 + (2008853907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253339361/10000000000 : ℝ)^4593 ≤ (33281820593333/100000000000000 : ℝ)^3569 := by
    have hnat : (4253339361 : ℕ)^4593*100000000000000^3569 ≤ 33281820593333^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253339361 10000000000 33281820593333 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500388653/10000000000 : ℝ)^4593 ≤ (3579004260069/10000000000000 : ℝ)^3569 := by
    have hnat : (4500388653 : ℕ)^4593*10000000000000^3569 ≤ 3579004260069^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500388653 10000000000 3579004260069 10000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008853907/5000000000 : ℝ)^4593 ≤ (7732034195511/25000000000000 : ℝ)^3569 := by
    have hnat : (2008853907 : ℕ)^4593*25000000000000^3569 ≤ 7732034195511^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008853907 5000000000 7732034195511 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253339361/10000000000 : ℝ), (4500388653/10000000000 : ℝ), (2008853907/5000000000 : ℝ)] ![(33281820593333/100000000000000 : ℝ), (3579004260069/10000000000000 : ℝ), (7732034195511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253339361/10000000000 : ℝ)|^4593 ≤ (33281820593333/100000000000000 : ℝ)^3569
        have hw : |(4253339361/10000000000 : ℝ)|=(4253339361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500388653/10000000000 : ℝ)|^4593 ≤ (3579004260069/10000000000000 : ℝ)^3569
        have hw : |(4500388653/10000000000 : ℝ)|=(4500388653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008853907/5000000000 : ℝ)|^4593 ≤ (7732034195511/25000000000000 : ℝ)^3569
        have hw : |(2008853907/5000000000 : ℝ)|=(2008853907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1548_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1553/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11043/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1553/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1553/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1553/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1553/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1553/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1553/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5503/50000 : ℝ) ^ (4591/1024 : ℝ) ≤ (5049440228944701/100000000000000000000 : ℝ) := by
    have hpowers : (5503/50000 : ℝ)^4591 ≤ (5049440228944701/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5503 : ℕ)^4591*100000000000000000000^1024 ≤ 5049440228944701^1024*50000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5503 50000 5049440228944701 100000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5503/50000 : ℝ)) (X := (5049440228944701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1553/10000 : ℝ) ^ (4591/1024 : ℝ) ≤ (23642825040367241/100000000000000000000 : ℝ) := by
    have hpowers : (1553/10000 : ℝ)^4591 ≤ (23642825040367241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1553 : ℕ)^4591*100000000000000000000^1024 ≤ 23642825040367241^1024*10000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1553 10000 23642825040367241 100000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1553/10000 : ℝ)) (X := (23642825040367241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005049440228944701/50000000000000000000 : ℝ) ≤ (10000225241731789/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (50005049440228944701/50000000000000000000 : ℝ)^1024 ≤ (10000225241731789/10000000000000000 : ℝ)^4591 := by
      have hnat : (50005049440228944701 : ℕ)^1024*10000000000000000^4591 ≤ 10000225241731789^4591*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005049440228944701 50000000000000000000 10000225241731789 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000225241731789/10000000000000000 : ℝ)) (X := (50005049440228944701/50000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014346132634655971/50000000000000000000 : ℝ) ≤ (2000127979112663/2000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (50014346132634655971/50000000000000000000 : ℝ)^1024 ≤ (2000127979112663/2000000000000000 : ℝ)^4591 := by
      have hnat : (50014346132634655971 : ℕ)^1024*2000000000000000^4591 ≤ 2000127979112663^4591*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014346132634655971 50000000000000000000 2000127979112663 2000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000127979112663/2000000000000000 : ℝ)) (X := (50014346132634655971/50000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023642825040367241/50000000000000000000 : ℝ) ≤ (10001054549394841/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (50023642825040367241/50000000000000000000 : ℝ)^1024 ≤ (10001054549394841/10000000000000000 : ℝ)^4591 := by
      have hnat : (50023642825040367241 : ℕ)^1024*10000000000000000^4591 ≤ 10001054549394841^4591*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023642825040367241 50000000000000000000 10001054549394841 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001054549394841/10000000000000000 : ℝ)) (X := (50023642825040367241/50000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5049440228944701/100000000000000000000 : ℝ) ≤ ((3769324302787921927/3770000000000000000 : ℝ)+2*(69108971921/75400000000000 : ℝ)*(5503/50000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (3769324302787921927/3770000000000000000 : ℝ)+2*(69108971921/75400000000000 : ℝ)*(5503/50000 : ℝ)=(10000225241731789/10000000000000000 : ℝ) by norm_num, show 1+2*(5049440228944701/100000000000000000000 : ℝ)=(50005049440228944701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23642825040367241/100000000000000000000 : ℝ)+(5049440228944701/100000000000000000000 : ℝ) ≤ ((3769324302787921927/3770000000000000000 : ℝ)+(69108971921/75400000000000 : ℝ)*((1553/10000 : ℝ)+(5503/50000 : ℝ)))^(4591/1024 : ℝ) := by
    rw [show (3769324302787921927/3770000000000000000 : ℝ)+(69108971921/75400000000000 : ℝ)*((1553/10000 : ℝ)+(5503/50000 : ℝ))=(2000127979112663/2000000000000000 : ℝ) by norm_num, show 1+(23642825040367241/100000000000000000000 : ℝ)+(5049440228944701/100000000000000000000 : ℝ)=(50014346132634655971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23642825040367241/100000000000000000000 : ℝ) ≤ ((3769324302787921927/3770000000000000000 : ℝ)+2*(69108971921/75400000000000 : ℝ)*(1553/10000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (3769324302787921927/3770000000000000000 : ℝ)+2*(69108971921/75400000000000 : ℝ)*(1553/10000 : ℝ)=(10001054549394841/10000000000000000 : ℝ) by norm_num, show 1+2*(23642825040367241/100000000000000000000 : ℝ)=(50023642825040367241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3769324302787921927/3770000000000000000 : ℝ)*(X 1 0+X 2 0)+(69108971921/75400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (5503/50000 : ℝ)) (hi := (1553/10000 : ℝ)) (c := (3769324302787921927/3770000000000000000 : ℝ)) (alpha := (69108971921/75400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3769324302787921927/3770000000000000000 : ℝ)*(X 0 1+X 2 1)+(69108971921/75400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (5503/50000 : ℝ)) (hi := (1553/10000 : ℝ)) (c := (3769324302787921927/3770000000000000000 : ℝ)) (alpha := (69108971921/75400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3769324302787921927/3770000000000000000 : ℝ)*(X 0 2+X 1 2)+(69108971921/75400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (5503/50000 : ℝ)) (hi := (1553/10000 : ℝ)) (c := (3769324302787921927/3770000000000000000 : ℝ)) (alpha := (69108971921/75400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1816080957/10000000000 : ℝ)*X 0 0+(1357205069/2500000000 : ℝ)*X 0 1+(1043809637/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349580141/10000000000 : ℝ)*X 1 0+(-961723211/5000000000 : ℝ)*X 1 1+(1304761939/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349580337/10000000000 : ℝ)*X 2 0+(5219047867/10000000000 : ℝ)*X 2 1+(-1923446011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((132914841/312500000 : ℝ)*X 0 0+(4015155011/10000000000 : ℝ)*X 0 1+(4502922681/10000000000 : ℝ)*X 0 2+(132914841/312500000 : ℝ)*X 1 0+(4015155011/10000000000 : ℝ)*X 1 1+(4502922681/10000000000 : ℝ)*X 1 2+(132914841/312500000 : ℝ)*X 2 0+(4015155011/10000000000 : ℝ)*X 2 1+(4502922681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1816108547/10000000000 : ℝ)*X 0 0+(5220137769/10000000000 : ℝ)*X 0 1+(5427722727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647116277/5000000000 : ℝ)*X 1 0+(-1714771457/10000000000 : ℝ)*X 1 1+(1356930689/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294232337/10000000000 : ℝ)*X 2 0+(5427722827/10000000000 : ℝ)*X 2 1+(-1714771657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4253339361/10000000000 : ℝ)*X 0 0+(4500388653/10000000000 : ℝ)*X 0 1+(2008853907/5000000000 : ℝ)*X 0 2+(4253339361/10000000000 : ℝ)*X 1 0+(4500388653/10000000000 : ℝ)*X 1 1+(2008853907/5000000000 : ℝ)*X 1 2+(4253339361/10000000000 : ℝ)*X 2 0+(4500388653/10000000000 : ℝ)*X 2 1+(2008853907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (905693506489131216792710589/94250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1516117517/100000000000000 : ℝ)*(base19) + (332988713/20000000000000 : ℝ)*(base23) + (4791917/25000000000000 : ℝ)*(upper3) + (13819681/100000000000000 : ℝ)*(upper4) + (54303187/12500000000000 : ℝ)*(upper5) + (1704321232541923/50000000000000 : ℝ)*(major0) + (1704321232541923/50000000000000 : ℝ)*(major1) + (1704321232541923/50000000000000 : ℝ)*(major2) + (2383544133262193/50000000000000 : ℝ)*(sp0) + (953422153463277/20000000000000 : ℝ)*(sp1) + (4767110618490337/100000000000000 : ℝ)*(sp2) + (128135392243593/6250000000000 : ℝ)*(sp3) + (6004227379/25000000000000 : ℝ)*(sp4) + (189078759/3125000000000 : ℝ)*(sp7) + (128135770401111/6250000000000 : ℝ)*(f.failure) + (2383556141716951/50000000000000 : ℝ)*(f.sum) + (3552171863367/1885000000000000000000000000 : ℝ)*base66 + (1895308949239404379/188500000000000000000000000000000 : ℝ)*base68 + (2238416749144404379/188500000000000000000000000000000 : ℝ)*base70 + (2030693897463904379/188500000000000000000000000000000 : ℝ)*base72 + (7523967884287/1885000000000000000000000000 : ℝ)*base74 + (2609568068787404379/188500000000000000000000000000000 : ℝ)*base76 + (2102284931497904379/188500000000000000000000000000000 : ℝ)*base78 + (1176671707390904379/188500000000000000000000000000000 : ℝ)*base80 + (3392316677911/942500000000000000000000000 : ℝ)*base82 + (2583263/312500000000000000000 : ℝ)*base89 + (2583263/312500000000000000000 : ℝ)*base91 + (2583263/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1702534783752868490164149/130000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (385842507/25000000000000 : ℝ)*(base19) + (1397567251/100000000000000 : ℝ)*(base23) + (88935857/50000000000000 : ℝ)*(upper3) + (67890611/100000000000000 : ℝ)*(lower4) + (69779731/20000000000000 : ℝ)*(upper5) + (68890670866447/2000000000000 : ℝ)*(major0) + (68890670866447/2000000000000 : ℝ)*(major1) + (68890670866447/2000000000000 : ℝ)*(major2) + (12981191899/50000000000000 : ℝ)*(sp1) + (18636459003/100000000000000 : ℝ)*(sp2) + (9408803062603/195312500000 : ℝ)*(sp4) + (481727966229891/10000000000000 : ℝ)*(sp5) + (2408643567013241/50000000000000 : ℝ)*(sp6) + (1035879741022287/50000000000000 : ℝ)*(sp7) + (1035879741022287/50000000000000 : ℝ)*(f.failure) + (9408803062603/195312500000 : ℝ)*(f.sum) + (1164133004941/377000000000000000000000000 : ℝ)*base65 + (125623634823006631/7540000000000000000000000000000 : ℝ)*base68 + (146918310188086631/7540000000000000000000000000000 : ℝ)*base70 + (52841101080646631/7540000000000000000000000000000 : ℝ)*base72 + (793022372457/377000000000000000000000000 : ℝ)*base74 + (48309603395126631/7540000000000000000000000000000 : ℝ)*base76 + (76761757014626631/7540000000000000000000000000000 : ℝ)*base78 + (91215713664746631/7540000000000000000000000000000 : ℝ)*base80 + (811957143499/188500000000000000000000000 : ℝ)*base82 + (35417671/2500000000000000000000 : ℝ)*base89 + (35417671/2500000000000000000000 : ℝ)*base91 + (35417671/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1548_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1553/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1548_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1548_s5_0 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1816112103/10000000000 : ℝ)*x 0 + (5428611577/10000000000 : ℝ)*x 1 + (5219236249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1816112103/10000000000 : ℝ)^4593 ≤ (11132161316839/100000000000000 : ℝ)^3569 := by
    have hnat : (1816112103 : ℕ)^4593*100000000000000^3569 ≤ 11132161316839^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816112103 10000000000 11132161316839 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428611577/10000000000 : ℝ)^4593 ≤ (11389560820753/25000000000000 : ℝ)^3569 := by
    have hnat : (5428611577 : ℕ)^4593*25000000000000^3569 ≤ 11389560820753^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428611577 10000000000 11389560820753 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219236249/10000000000 : ℝ)^4593 ≤ (21654797695729/50000000000000 : ℝ)^3569 := by
    have hnat : (5219236249 : ℕ)^4593*50000000000000^3569 ≤ 21654797695729^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219236249 10000000000 21654797695729 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1816112103/10000000000 : ℝ), (5428611577/10000000000 : ℝ), (5219236249/10000000000 : ℝ)] ![(11132161316839/100000000000000 : ℝ), (11389560820753/25000000000000 : ℝ), (21654797695729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1816112103/10000000000 : ℝ)|^4593 ≤ (11132161316839/100000000000000 : ℝ)^3569
        have hw : |(-1816112103/10000000000 : ℝ)|=(1816112103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428611577/10000000000 : ℝ)|^4593 ≤ (11389560820753/25000000000000 : ℝ)^3569
        have hw : |(5428611577/10000000000 : ℝ)|=(5428611577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219236249/10000000000 : ℝ)|^4593 ≤ (21654797695729/50000000000000 : ℝ)^3569
        have hw : |(5219236249/10000000000 : ℝ)|=(5219236249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s5_1 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674762541/5000000000 : ℝ)*x 0 + (-961634617/5000000000 : ℝ)*x 1 + (2609618133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674762541/5000000000 : ℝ)^4593 ≤ (22352945968099/50000000000000 : ℝ)^3569 := by
    have hnat : (2674762541 : ℕ)^4593*50000000000000^3569 ≤ 22352945968099^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674762541 5000000000 22352945968099 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961634617/5000000000 : ℝ)^4593 ≤ (93629003743/781250000000 : ℝ)^3569 := by
    have hnat : (961634617 : ℕ)^4593*781250000000^3569 ≤ 93629003743^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961634617 5000000000 93629003743 781250000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609618133/5000000000 : ℝ)^4593 ≤ (43309595572999/100000000000000 : ℝ)^3569 := by
    have hnat : (2609618133 : ℕ)^4593*100000000000000^3569 ≤ 43309595572999^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609618133 5000000000 43309595572999 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674762541/5000000000 : ℝ), (-961634617/5000000000 : ℝ), (2609618133/5000000000 : ℝ)] ![(22352945968099/50000000000000 : ℝ), (93629003743/781250000000 : ℝ), (43309595572999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674762541/5000000000 : ℝ)|^4593 ≤ (22352945968099/50000000000000 : ℝ)^3569
        have hw : |(2674762541/5000000000 : ℝ)|=(2674762541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-961634617/5000000000 : ℝ)|^4593 ≤ (93629003743/781250000000 : ℝ)^3569
        have hw : |(-961634617/5000000000 : ℝ)|=(961634617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609618133/5000000000 : ℝ)|^4593 ≤ (43309595572999/100000000000000 : ℝ)^3569
        have hw : |(2609618133/5000000000 : ℝ)|=(2609618133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s5_2 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337381273/2500000000 : ℝ)*x 0 + (5219236257/10000000000 : ℝ)*x 1 + (-120204327/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337381273/2500000000 : ℝ)^4593 ≤ (8941178408749/20000000000000 : ℝ)^3569 := by
    have hnat : (1337381273 : ℕ)^4593*20000000000000^3569 ≤ 8941178408749^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337381273 2500000000 8941178408749 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219236257/10000000000 : ℝ)^4593 ≤ (43309595476889/100000000000000 : ℝ)^3569 := by
    have hnat : (5219236257 : ℕ)^4593*100000000000000^3569 ≤ 43309595476889^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219236257 10000000000 43309595476889 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120204327/625000000 : ℝ)^4593 ≤ (5992256231533/50000000000000 : ℝ)^3569 := by
    have hnat : (120204327 : ℕ)^4593*50000000000000^3569 ≤ 5992256231533^3569*625000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120204327 625000000 5992256231533 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337381273/2500000000 : ℝ), (5219236257/10000000000 : ℝ), (-120204327/625000000 : ℝ)] ![(8941178408749/20000000000000 : ℝ), (43309595476889/100000000000000 : ℝ), (5992256231533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337381273/2500000000 : ℝ)|^4593 ≤ (8941178408749/20000000000000 : ℝ)^3569
        have hw : |(1337381273/2500000000 : ℝ)|=(1337381273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219236257/10000000000 : ℝ)|^4593 ≤ (43309595476889/100000000000000 : ℝ)^3569
        have hw : |(5219236257/10000000000 : ℝ)|=(5219236257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120204327/625000000 : ℝ)|^4593 ≤ (5992256231533/50000000000000 : ℝ)^3569
        have hw : |(-120204327/625000000 : ℝ)|=(120204327/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s5_3 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66457727/156250000 : ℝ)*x 0 + (803122851/2000000000 : ℝ)*x 1 + (2251229493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66457727/156250000 : ℝ)^4593 ≤ (33281369128339/100000000000000 : ℝ)^3569 := by
    have hnat : (66457727 : ℕ)^4593*100000000000000^3569 ≤ 33281369128339^3569*156250000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66457727 156250000 33281369128339 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803122851/2000000000 : ℝ)^4593 ≤ (30907398248687/100000000000000 : ℝ)^3569 := by
    have hnat : (803122851 : ℕ)^4593*100000000000000^3569 ≤ 30907398248687^3569*2000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803122851 2000000000 30907398248687 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251229493/5000000000 : ℝ)^4593 ≤ (7162246520109/20000000000000 : ℝ)^3569 := by
    have hnat : (2251229493 : ℕ)^4593*20000000000000^3569 ≤ 7162246520109^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251229493 5000000000 7162246520109 20000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66457727/156250000 : ℝ), (803122851/2000000000 : ℝ), (2251229493/5000000000 : ℝ)] ![(33281369128339/100000000000000 : ℝ), (30907398248687/100000000000000 : ℝ), (7162246520109/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66457727/156250000 : ℝ)|^4593 ≤ (33281369128339/100000000000000 : ℝ)^3569
        have hw : |(66457727/156250000 : ℝ)|=(66457727/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803122851/2000000000 : ℝ)|^4593 ≤ (30907398248687/100000000000000 : ℝ)^3569
        have hw : |(803122851/2000000000 : ℝ)|=(803122851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251229493/5000000000 : ℝ)|^4593 ≤ (7162246520109/20000000000000 : ℝ)^3569
        have hw : |(2251229493/5000000000 : ℝ)|=(2251229493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s5_4 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-908069717/5000000000 : ℝ)*x 0 + (5220322109/10000000000 : ℝ)*x 1 + (43420143/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908069717/5000000000 : ℝ)^4593 ≤ (5566188457039/50000000000000 : ℝ)^3569 := by
    have hnat : (908069717 : ℕ)^4593*50000000000000^3569 ≤ 5566188457039^3569*5000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908069717 5000000000 5566188457039 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220322109/10000000000 : ℝ)^4593 ≤ (21660595771267/50000000000000 : ℝ)^3569 := by
    have hnat : (5220322109 : ℕ)^4593*50000000000000^3569 ≤ 21660595771267^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220322109 10000000000 21660595771267 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43420143/80000000 : ℝ)^4593 ≤ (11386607881177/25000000000000 : ℝ)^3569 := by
    have hnat : (43420143 : ℕ)^4593*25000000000000^3569 ≤ 11386607881177^3569*80000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43420143 80000000 11386607881177 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-908069717/5000000000 : ℝ), (5220322109/10000000000 : ℝ), (43420143/80000000 : ℝ)] ![(5566188457039/50000000000000 : ℝ), (21660595771267/50000000000000 : ℝ), (11386607881177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-908069717/5000000000 : ℝ)|^4593 ≤ (5566188457039/50000000000000 : ℝ)^3569
        have hw : |(-908069717/5000000000 : ℝ)|=(908069717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220322109/10000000000 : ℝ)|^4593 ≤ (21660595771267/50000000000000 : ℝ)^3569
        have hw : |(5220322109/10000000000 : ℝ)|=(5220322109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43420143/80000000 : ℝ)|^4593 ≤ (11386607881177/25000000000000 : ℝ)^3569
        have hw : |(43420143/80000000 : ℝ)|=(43420143/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s5_5 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294282731/10000000000 : ℝ)*x 0 + (-1714987593/10000000000 : ℝ)*x 1 + (5427517639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294282731/10000000000 : ℝ)^4593 ≤ (22056328892129/50000000000000 : ℝ)^3569 := by
    have hnat : (5294282731 : ℕ)^4593*50000000000000^3569 ≤ 22056328892129^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294282731 10000000000 22056328892129 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714987593/10000000000 : ℝ)^4593 ≤ (10340913229697/100000000000000 : ℝ)^3569 := by
    have hnat : (1714987593 : ℕ)^4593*100000000000000^3569 ≤ 10340913229697^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714987593 10000000000 10340913229697 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427517639/10000000000 : ℝ)^4593 ≤ (45546428976029/100000000000000 : ℝ)^3569 := by
    have hnat : (5427517639 : ℕ)^4593*100000000000000^3569 ≤ 45546428976029^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427517639 10000000000 45546428976029 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294282731/10000000000 : ℝ), (-1714987593/10000000000 : ℝ), (5427517639/10000000000 : ℝ)] ![(22056328892129/50000000000000 : ℝ), (10340913229697/100000000000000 : ℝ), (45546428976029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294282731/10000000000 : ℝ)|^4593 ≤ (22056328892129/50000000000000 : ℝ)^3569
        have hw : |(5294282731/10000000000 : ℝ)|=(5294282731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1714987593/10000000000 : ℝ)|^4593 ≤ (10340913229697/100000000000000 : ℝ)^3569
        have hw : |(-1714987593/10000000000 : ℝ)|=(1714987593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427517639/10000000000 : ℝ)|^4593 ≤ (45546428976029/100000000000000 : ℝ)^3569
        have hw : |(5427517639/10000000000 : ℝ)|=(5427517639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s5_6 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323570607/2500000000 : ℝ)*x 0 + (5427517769/10000000000 : ℝ)*x 1 + (-171498783/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323570607/2500000000 : ℝ)^4593 ≤ (22056327267633/50000000000000 : ℝ)^3569 := by
    have hnat : (1323570607 : ℕ)^4593*50000000000000^3569 ≤ 22056327267633^3569*2500000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323570607 2500000000 22056327267633 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427517769/10000000000 : ℝ)^4593 ≤ (22773215189981/50000000000000 : ℝ)^3569 := by
    have hnat : (5427517769 : ℕ)^4593*50000000000000^3569 ≤ 22773215189981^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427517769 10000000000 22773215189981 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171498783/1000000000 : ℝ)^4593 ≤ (5170457534379/50000000000000 : ℝ)^3569 := by
    have hnat : (171498783 : ℕ)^4593*50000000000000^3569 ≤ 5170457534379^3569*1000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171498783 1000000000 5170457534379 50000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323570607/2500000000 : ℝ), (5427517769/10000000000 : ℝ), (-171498783/1000000000 : ℝ)] ![(22056327267633/50000000000000 : ℝ), (22773215189981/50000000000000 : ℝ), (5170457534379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323570607/2500000000 : ℝ)|^4593 ≤ (22056327267633/50000000000000 : ℝ)^3569
        have hw : |(1323570607/2500000000 : ℝ)|=(1323570607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427517769/10000000000 : ℝ)|^4593 ≤ (22773215189981/50000000000000 : ℝ)^3569
        have hw : |(5427517769/10000000000 : ℝ)|=(5427517769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171498783/1000000000 : ℝ)|^4593 ≤ (5170457534379/50000000000000 : ℝ)^3569
        have hw : |(-171498783/1000000000 : ℝ)|=(171498783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1548_s5_7 (p : ℝ) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253358607/10000000000 : ℝ)*x 0 + (4499934147/10000000000 : ℝ)*x 1 + (4018157781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253358607/10000000000 : ℝ)^4593 ≤ (8320503599887/25000000000000 : ℝ)^3569 := by
    have hnat : (4253358607 : ℕ)^4593*25000000000000^3569 ≤ 8320503599887^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253358607 10000000000 8320503599887 25000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499934147/10000000000 : ℝ)^4593 ≤ (35785391075039/100000000000000 : ℝ)^3569 := by
    have hnat : (4499934147 : ℕ)^4593*100000000000000^3569 ≤ 35785391075039^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499934147 10000000000 35785391075039 100000000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018157781/10000000000 : ℝ)^4593 ≤ (1933287156481/6250000000000 : ℝ)^3569 := by
    have hnat : (4018157781 : ℕ)^4593*6250000000000^3569 ≤ 1933287156481^3569*10000000000^4593 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018157781 10000000000 1933287156481 6250000000000 4593 3569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4593/1024 : ℝ)) 4593 3569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253358607/10000000000 : ℝ), (4499934147/10000000000 : ℝ), (4018157781/10000000000 : ℝ)] ![(8320503599887/25000000000000 : ℝ), (35785391075039/100000000000000 : ℝ), (1933287156481/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253358607/10000000000 : ℝ)|^4593 ≤ (8320503599887/25000000000000 : ℝ)^3569
        have hw : |(4253358607/10000000000 : ℝ)|=(4253358607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499934147/10000000000 : ℝ)|^4593 ≤ (35785391075039/100000000000000 : ℝ)^3569
        have hw : |(4499934147/10000000000 : ℝ)|=(4499934147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018157781/10000000000 : ℝ)|^4593 ≤ (1933287156481/6250000000000 : ℝ)^3569
        have hw : |(4018157781/10000000000 : ℝ)|=(4018157781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1548_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11047/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11043/100000 : ℝ) ^ (4591/1024 : ℝ) ≤ (640749222000501/12500000000000000000 : ℝ) := by
    have hpowers : (11043/100000 : ℝ)^4591 ≤ (640749222000501/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11043 : ℕ)^4591*12500000000000000000^1024 ≤ 640749222000501^1024*100000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11043 100000 640749222000501 12500000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11043/100000 : ℝ)) (X := (640749222000501/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4591/1024 : ℝ) ≤ (11685513359625881/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4591 ≤ (11685513359625881/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4591*50000000000000000000^1024 ≤ 11685513359625881^1024*10000^4591 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 11685513359625881 50000000000000000000 4591 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (11685513359625881/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250640749222000501/6250000000000000000 : ℝ) ≤ (10000228656440361/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (6250640749222000501/6250000000000000000 : ℝ)^1024 ≤ (10000228656440361/10000000000000000 : ℝ)^4591 := by
      have hnat : (6250640749222000501 : ℕ)^1024*10000000000000000^4591 ≤ 10000228656440361^4591*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250640749222000501 6250000000000000000 10000228656440361 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000228656440361/10000000000000000 : ℝ)) (X := (6250640749222000501/6250000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002849702049525577/10000000000000000000 : ℝ) ≤ (10000635541691787/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (10002849702049525577/10000000000000000000 : ℝ)^1024 ≤ (10000635541691787/10000000000000000 : ℝ)^4591 := by
      have hnat : (10002849702049525577 : ℕ)^1024*10000000000000000^4591 ≤ 10000635541691787^4591*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002849702049525577 10000000000000000000 10000635541691787 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000635541691787/10000000000000000 : ℝ)) (X := (10002849702049525577/10000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011685513359625881/25000000000000000000 : ℝ) ≤ (10001042426943213/10000000000000000 : ℝ) ^ (4591/1024 : ℝ) := by
    have hpowers : (25011685513359625881/25000000000000000000 : ℝ)^1024 ≤ (10001042426943213/10000000000000000 : ℝ)^4591 := by
      have hnat : (25011685513359625881 : ℕ)^1024*10000000000000000^4591 ≤ 10001042426943213^4591*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011685513359625881 25000000000000000000 10001042426943213 10000000000000000 1024 4591 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001042426943213/10000000000000000 : ℝ)) (X := (25011685513359625881/25000000000000000000 : ℝ)) (by norm_num) 4591 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(640749222000501/12500000000000000000 : ℝ) ≤ ((44462030367527290731/44470000000000000000 : ℝ)+2*(203442625713/222350000000000 : ℝ)*(11043/100000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (44462030367527290731/44470000000000000000 : ℝ)+2*(203442625713/222350000000000 : ℝ)*(11043/100000 : ℝ)=(10000228656440361/10000000000000000 : ℝ) by norm_num, show 1+2*(640749222000501/12500000000000000000 : ℝ)=(6250640749222000501/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11685513359625881/50000000000000000000 : ℝ)+(640749222000501/12500000000000000000 : ℝ) ≤ ((44462030367527290731/44470000000000000000 : ℝ)+(203442625713/222350000000000 : ℝ)*((1549/10000 : ℝ)+(11043/100000 : ℝ)))^(4591/1024 : ℝ) := by
    rw [show (44462030367527290731/44470000000000000000 : ℝ)+(203442625713/222350000000000 : ℝ)*((1549/10000 : ℝ)+(11043/100000 : ℝ))=(10000635541691787/10000000000000000 : ℝ) by norm_num, show 1+(11685513359625881/50000000000000000000 : ℝ)+(640749222000501/12500000000000000000 : ℝ)=(10002849702049525577/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11685513359625881/50000000000000000000 : ℝ) ≤ ((44462030367527290731/44470000000000000000 : ℝ)+2*(203442625713/222350000000000 : ℝ)*(1549/10000 : ℝ))^(4591/1024 : ℝ) := by
    rw [show (44462030367527290731/44470000000000000000 : ℝ)+2*(203442625713/222350000000000 : ℝ)*(1549/10000 : ℝ)=(10001042426943213/10000000000000000 : ℝ) by norm_num, show 1+2*(11685513359625881/50000000000000000000 : ℝ)=(25011685513359625881/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44462030367527290731/44470000000000000000 : ℝ)*(X 1 0+X 2 0)+(203442625713/222350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44462030367527290731/44470000000000000000 : ℝ)) (alpha := (203442625713/222350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44462030367527290731/44470000000000000000 : ℝ)*(X 0 1+X 2 1)+(203442625713/222350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44462030367527290731/44470000000000000000 : ℝ)) (alpha := (203442625713/222350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44462030367527290731/44470000000000000000 : ℝ)*(X 0 2+X 1 2)+(203442625713/222350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4591/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (44462030367527290731/44470000000000000000 : ℝ)) (alpha := (203442625713/222350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1816112103/10000000000 : ℝ)*X 0 0+(5428611577/10000000000 : ℝ)*X 0 1+(5219236249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674762541/5000000000 : ℝ)*X 1 0+(-961634617/5000000000 : ℝ)*X 1 1+(2609618133/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337381273/2500000000 : ℝ)*X 2 0+(5219236257/10000000000 : ℝ)*X 2 1+(-120204327/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((66457727/156250000 : ℝ)*X 0 0+(803122851/2000000000 : ℝ)*X 0 1+(2251229493/5000000000 : ℝ)*X 0 2+(66457727/156250000 : ℝ)*X 1 0+(803122851/2000000000 : ℝ)*X 1 1+(2251229493/5000000000 : ℝ)*X 1 2+(66457727/156250000 : ℝ)*X 2 0+(803122851/2000000000 : ℝ)*X 2 1+(2251229493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-908069717/5000000000 : ℝ)*X 0 0+(5220322109/10000000000 : ℝ)*X 0 1+(43420143/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294282731/10000000000 : ℝ)*X 1 0+(-1714987593/10000000000 : ℝ)*X 1 1+(5427517639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323570607/2500000000 : ℝ)*X 2 0+(5427517769/10000000000 : ℝ)*X 2 1+(-171498783/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4253358607/10000000000 : ℝ)*X 0 0+(4499934147/10000000000 : ℝ)*X 0 1+(4018157781/10000000000 : ℝ)*X 0 2+(4253358607/10000000000 : ℝ)*X 1 0+(4499934147/10000000000 : ℝ)*X 1 1+(4018157781/10000000000 : ℝ)*X 1 2+(4253358607/10000000000 : ℝ)*X 2 0+(4499934147/10000000000 : ℝ)*X 2 1+(4018157781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1548_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5499729985133764517698838919/555875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106161/6250000000 : ℝ)*(base19) + (795716649/50000000000000 : ℝ)*(base23) + (7761553/12500000000000 : ℝ)*(lower2) + (122255433/50000000000000 : ℝ)*(upper3) + (32734791/20000000000000 : ℝ)*(upper5) + (1707558846276617/50000000000000 : ℝ)*(major0) + (1707558846276617/50000000000000 : ℝ)*(major1) + (1707558846276617/50000000000000 : ℝ)*(major2) + (4776140480720449/100000000000000 : ℝ)*(sp0) + (4776166420572557/100000000000000 : ℝ)*(sp1) + (4776166527715259/100000000000000 : ℝ)*(sp2) + (1027027130800013/50000000000000 : ℝ)*(sp3) + (6909607027/25000000000000 : ℝ)*(sp4) + (6337281853/50000000000000 : ℝ)*(sp7) + (2054066936163733/100000000000000 : ℝ)*(f.failure) + (1194042029787139/25000000000000 : ℝ)*(f.sum) + (129396329604199/22235000000000000000000000000 : ℝ)*base65 + (24985166602650837027/2223500000000000000000000000000000 : ℝ)*base67 + (7467323929399837027/2223500000000000000000000000000000 : ℝ)*base69 + (14608464123106337027/2223500000000000000000000000000000 : ℝ)*base71 + (117691308093147/11117500000000000000000000000 : ℝ)*base73 + (25588924837466337027/2223500000000000000000000000000000 : ℝ)*base75 + (21324758986687337027/2223500000000000000000000000000000 : ℝ)*base77 + (19937243868322162973/2223500000000000000000000000000000 : ℝ)*base80 + (50690684207097/11117500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15932989/5000000000000000000000 : ℝ)*base89 + (15932989/5000000000000000000000 : ℝ)*base91 + (15932989/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114142940120273043980211/22235000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18521997/2500000000000 : ℝ)*(base19) + (138339971/20000000000000 : ℝ)*(base23) + (72296337/50000000000000 : ℝ)*(lower1) + (142942729/100000000000000 : ℝ)*(lower4) + (86544721/100000000000000 : ℝ)*(upper5) + (1725497884501157/50000000000000 : ℝ)*(major0) + (1725497884501157/50000000000000 : ℝ)*(major1) + (1725497884501157/50000000000000 : ℝ)*(major2) + (131366321/50000000000000 : ℝ)*(sp0) + (4116731007/100000000000000 : ℝ)*(sp1) + (4826344832460717/100000000000000 : ℝ)*(sp4) + (4826340237582471/100000000000000 : ℝ)*(sp5) + (4826344403493503/100000000000000 : ℝ)*(sp6) + (415129254339049/20000000000000 : ℝ)*(sp7) + (415129254339049/20000000000000 : ℝ)*(f.failure) + (4826345095193359/100000000000000 : ℝ)*(f.sum) + (13258283943821/22235000000000000000000000000 : ℝ)*base66 + (15689496957413924233/2223500000000000000000000000000000 : ℝ)*base68 + (6437042022049924233/2223500000000000000000000000000000 : ℝ)*base70 + (5679366635731924233/2223500000000000000000000000000000 : ℝ)*base72 + (47142053097813/11117500000000000000000000000 : ℝ)*base74 + (14694991696797075767/2223500000000000000000000000000000 : ℝ)*base75 + (8667012438356575767/2223500000000000000000000000000000 : ℝ)*base77 + (7963059402416075767/2223500000000000000000000000000000 : ℝ)*base79 + (84758026981161/22235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11983/1000000000000000000000 : ℝ)*base90 + (11983/1000000000000000000000 : ℝ)*base92 + (11983/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1548_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1548_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1548_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10689/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1548_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1548_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1548_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4591/1024 : ℝ) ≤ p) (hpb : p ≤ (4593/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83130633/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7937/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10689/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11047/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1548_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
