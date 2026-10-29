-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1619_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:46.892641+00:00
-- url     : https://prove2.me/submissions/2e23f832-63c3-44b8-ba14-1f0e0be28dc8

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
theorem support_rectangle_w1619_s0_0 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-309729537/2000000000 : ℝ)*x 0 + (116501119/200000000 : ℝ)*x 1 + (4899679261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309729537/2000000000 : ℝ)^4795 ≤ (9332274326317/100000000000000 : ℝ)^3771 := by
    have hnat : (309729537 : ℕ)^4795*100000000000000^3771 ≤ 9332274326317^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309729537 2000000000 9332274326317 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116501119/200000000 : ℝ)^4795 ≤ (25150017097033/50000000000000 : ℝ)^3771 := by
    have hnat : (116501119 : ℕ)^4795*50000000000000^3771 ≤ 25150017097033^3771*200000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116501119 200000000 25150017097033 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4899679261/10000000000 : ℝ)^4795 ≤ (20183845732123/50000000000000 : ℝ)^3771 := by
    have hnat : (4899679261 : ℕ)^4795*50000000000000^3771 ≤ 20183845732123^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899679261 10000000000 20183845732123 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-309729537/2000000000 : ℝ), (116501119/200000000 : ℝ), (4899679261/10000000000 : ℝ)] ![(9332274326317/100000000000000 : ℝ), (25150017097033/50000000000000 : ℝ), (20183845732123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-309729537/2000000000 : ℝ)|^4795 ≤ (9332274326317/100000000000000 : ℝ)^3771
        have hw : |(-309729537/2000000000 : ℝ)|=(309729537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116501119/200000000 : ℝ)|^4795 ≤ (25150017097033/50000000000000 : ℝ)^3771
        have hw : |(116501119/200000000 : ℝ)|=(116501119/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4899679261/10000000000 : ℝ)|^4795 ≤ (20183845732123/50000000000000 : ℝ)^3771
        have hw : |(4899679261/10000000000 : ℝ)|=(4899679261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s0_1 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5450022781/10000000000 : ℝ)*x 0 + (-2059973559/10000000000 : ℝ)*x 1 + (195987173/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5450022781/10000000000 : ℝ)^4795 ≤ (23109382296739/50000000000000 : ℝ)^3771 := by
    have hnat : (5450022781 : ℕ)^4795*50000000000000^3771 ≤ 23109382296739^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450022781 10000000000 23109382296739 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059973559/10000000000 : ℝ)^4795 ≤ (13413543261933/100000000000000 : ℝ)^3771 := by
    have hnat : (2059973559 : ℕ)^4795*100000000000000^3771 ≤ 13413543261933^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059973559 10000000000 13413543261933 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195987173/400000000 : ℝ)^4795 ≤ (20183846067357/50000000000000 : ℝ)^3771 := by
    have hnat : (195987173 : ℕ)^4795*50000000000000^3771 ≤ 20183846067357^3771*400000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195987173 400000000 20183846067357 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5450022781/10000000000 : ℝ), (-2059973559/10000000000 : ℝ), (195987173/400000000 : ℝ)] ![(23109382296739/50000000000000 : ℝ), (13413543261933/100000000000000 : ℝ), (20183846067357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5450022781/10000000000 : ℝ)|^4795 ≤ (23109382296739/50000000000000 : ℝ)^3771
        have hw : |(5450022781/10000000000 : ℝ)|=(5450022781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059973559/10000000000 : ℝ)|^4795 ≤ (13413543261933/100000000000000 : ℝ)^3771
        have hw : |(-2059973559/10000000000 : ℝ)|=(2059973559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(195987173/400000000 : ℝ)|^4795 ≤ (20183846067357/50000000000000 : ℝ)^3771
        have hw : |(195987173/400000000 : ℝ)|=(195987173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s0_2 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218000903/400000000 : ℝ)*x 0 + (4899679359/10000000000 : ℝ)*x 1 + (-257496723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218000903/400000000 : ℝ)^4795 ≤ (11554690593029/25000000000000 : ℝ)^3771 := by
    have hnat : (218000903 : ℕ)^4795*25000000000000^3771 ≤ 11554690593029^3771*400000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218000903 400000000 11554690593029 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4899679359/10000000000 : ℝ)^4795 ≤ (40367692490901/100000000000000 : ℝ)^3771 := by
    have hnat : (4899679359 : ℕ)^4795*100000000000000^3771 ≤ 40367692490901^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899679359 10000000000 40367692490901 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257496723/1250000000 : ℝ)^4795 ≤ (13413545124863/100000000000000 : ℝ)^3771 := by
    have hnat : (257496723 : ℕ)^4795*100000000000000^3771 ≤ 13413545124863^3771*1250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257496723 1250000000 13413545124863 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218000903/400000000 : ℝ), (4899679359/10000000000 : ℝ), (-257496723/1250000000 : ℝ)] ![(11554690593029/25000000000000 : ℝ), (40367692490901/100000000000000 : ℝ), (13413545124863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218000903/400000000 : ℝ)|^4795 ≤ (11554690593029/25000000000000 : ℝ)^3771
        have hw : |(218000903/400000000 : ℝ)|=(218000903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4899679359/10000000000 : ℝ)|^4795 ≤ (40367692490901/100000000000000 : ℝ)^3771
        have hw : |(4899679359/10000000000 : ℝ)|=(4899679359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257496723/1250000000 : ℝ)|^4795 ≤ (13413545124863/100000000000000 : ℝ)^3771
        have hw : |(-257496723/1250000000 : ℝ)|=(257496723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s0_3 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164215509/400000000 : ℝ)*x 0 + (3075855749/10000000000 : ℝ)*x 1 + (1075359049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164215509/400000000 : ℝ)^4795 ≤ (128950206309/400000000000 : ℝ)^3771 := by
    have hnat : (164215509 : ℕ)^4795*400000000000^3771 ≤ 128950206309^3771*400000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164215509 400000000 128950206309 400000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3075855749/10000000000 : ℝ)^4795 ≤ (5582968453539/25000000000000 : ℝ)^3771 := by
    have hnat : (3075855749 : ℕ)^4795*25000000000000^3771 ≤ 5582968453539^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3075855749 10000000000 5582968453539 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075359049/2000000000 : ℝ)^4795 ≤ (5678821825239/12500000000000 : ℝ)^3771 := by
    have hnat : (1075359049 : ℕ)^4795*12500000000000^3771 ≤ 5678821825239^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075359049 2000000000 5678821825239 12500000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164215509/400000000 : ℝ), (3075855749/10000000000 : ℝ), (1075359049/2000000000 : ℝ)] ![(128950206309/400000000000 : ℝ), (5582968453539/25000000000000 : ℝ), (5678821825239/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164215509/400000000 : ℝ)|^4795 ≤ (128950206309/400000000000 : ℝ)^3771
        have hw : |(164215509/400000000 : ℝ)|=(164215509/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3075855749/10000000000 : ℝ)|^4795 ≤ (5582968453539/25000000000000 : ℝ)^3771
        have hw : |(3075855749/10000000000 : ℝ)|=(3075855749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075359049/2000000000 : ℝ)|^4795 ≤ (5678821825239/12500000000000 : ℝ)^3771
        have hw : |(1075359049/2000000000 : ℝ)|=(1075359049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s0_4 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-310264321/2000000000 : ℝ)*x 0 + (4923001319/10000000000 : ℝ)*x 1 + (290045487/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (310264321/2000000000 : ℝ)^4795 ≤ (9352767872453/100000000000000 : ℝ)^3771 := by
    have hnat : (310264321 : ℕ)^4795*100000000000000^3771 ≤ 9352767872453^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310264321 2000000000 9352767872453 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4923001319/10000000000 : ℝ)^4795 ≤ (20306086332221/50000000000000 : ℝ)^3771 := by
    have hnat : (4923001319 : ℕ)^4795*50000000000000^3771 ≤ 20306086332221^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923001319 10000000000 20306086332221 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290045487/500000000 : ℝ)^4795 ≤ (312719121527/625000000000 : ℝ)^3771 := by
    have hnat : (290045487 : ℕ)^4795*625000000000^3771 ≤ 312719121527^3771*500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290045487 500000000 312719121527 625000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-310264321/2000000000 : ℝ), (4923001319/10000000000 : ℝ), (290045487/500000000 : ℝ)] ![(9352767872453/100000000000000 : ℝ), (20306086332221/50000000000000 : ℝ), (312719121527/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-310264321/2000000000 : ℝ)|^4795 ≤ (9352767872453/100000000000000 : ℝ)^3771
        have hw : |(-310264321/2000000000 : ℝ)|=(310264321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4923001319/10000000000 : ℝ)|^4795 ≤ (20306086332221/50000000000000 : ℝ)^3771
        have hw : |(4923001319/10000000000 : ℝ)|=(4923001319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(290045487/500000000 : ℝ)|^4795 ≤ (312719121527/625000000000 : ℝ)^3771
        have hw : |(290045487/500000000 : ℝ)|=(290045487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s0_5 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197317957/10000000000 : ℝ)*x 0 + (-1158743291/10000000000 : ℝ)*x 1 + (1450227443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197317957/10000000000 : ℝ)^4795 ≤ (21755561186649/50000000000000 : ℝ)^3771 := by
    have hnat : (5197317957 : ℕ)^4795*50000000000000^3771 ≤ 21755561186649^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197317957 10000000000 21755561186649 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1158743291/10000000000 : ℝ)^4795 ≤ (3226908905617/50000000000000 : ℝ)^3771 := by
    have hnat : (1158743291 : ℕ)^4795*50000000000000^3771 ≤ 3226908905617^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158743291 10000000000 3226908905617 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1450227443/2500000000 : ℝ)^4795 ≤ (25017529897641/50000000000000 : ℝ)^3771 := by
    have hnat : (1450227443 : ℕ)^4795*50000000000000^3771 ≤ 25017529897641^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450227443 2500000000 25017529897641 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197317957/10000000000 : ℝ), (-1158743291/10000000000 : ℝ), (1450227443/2500000000 : ℝ)] ![(21755561186649/50000000000000 : ℝ), (3226908905617/50000000000000 : ℝ), (25017529897641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197317957/10000000000 : ℝ)|^4795 ≤ (21755561186649/50000000000000 : ℝ)^3771
        have hw : |(5197317957/10000000000 : ℝ)|=(5197317957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1158743291/10000000000 : ℝ)|^4795 ≤ (3226908905617/50000000000000 : ℝ)^3771
        have hw : |(-1158743291/10000000000 : ℝ)|=(1158743291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1450227443/2500000000 : ℝ)|^4795 ≤ (25017529897641/50000000000000 : ℝ)^3771
        have hw : |(1450227443/2500000000 : ℝ)|=(1450227443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s0_6 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197317949/10000000000 : ℝ)*x 0 + (2900455127/5000000000 : ℝ)*x 1 + (-579371279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197317949/10000000000 : ℝ)^4795 ≤ (43511122288137/100000000000000 : ℝ)^3771 := by
    have hnat : (5197317949 : ℕ)^4795*100000000000000^3771 ≤ 43511122288137^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197317949 10000000000 43511122288137 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2900455127/5000000000 : ℝ)^4795 ≤ (50035065081651/100000000000000 : ℝ)^3771 := by
    have hnat : (2900455127 : ℕ)^4795*100000000000000^3771 ≤ 50035065081651^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2900455127 5000000000 50035065081651 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579371279/5000000000 : ℝ)^4795 ≤ (6453812620061/100000000000000 : ℝ)^3771 := by
    have hnat : (579371279 : ℕ)^4795*100000000000000^3771 ≤ 6453812620061^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579371279 5000000000 6453812620061 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197317949/10000000000 : ℝ), (2900455127/5000000000 : ℝ), (-579371279/5000000000 : ℝ)] ![(43511122288137/100000000000000 : ℝ), (50035065081651/100000000000000 : ℝ), (6453812620061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197317949/10000000000 : ℝ)|^4795 ≤ (43511122288137/100000000000000 : ℝ)^3771
        have hw : |(5197317949/10000000000 : ℝ)|=(5197317949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2900455127/5000000000 : ℝ)|^4795 ≤ (50035065081651/100000000000000 : ℝ)^3771
        have hw : |(2900455127/5000000000 : ℝ)|=(2900455127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-579371279/5000000000 : ℝ)|^4795 ≤ (6453812620061/100000000000000 : ℝ)^3771
        have hw : |(-579371279/5000000000 : ℝ)|=(579371279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s0_7 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4112035377/10000000000 : ℝ)*x 0 + (2659401823/5000000000 : ℝ)*x 1 + (627179107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112035377/10000000000 : ℝ)^4795 ≤ (32303941728469/100000000000000 : ℝ)^3771 := by
    have hnat : (4112035377 : ℕ)^4795*100000000000000^3771 ≤ 32303941728469^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112035377 10000000000 32303941728469 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2659401823/5000000000 : ℝ)^4795 ≤ (22404220414191/50000000000000 : ℝ)^3771 := by
    have hnat : (2659401823 : ℕ)^4795*50000000000000^3771 ≤ 22404220414191^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659401823 5000000000 22404220414191 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627179107/2000000000 : ℝ)^4795 ≤ (11443808717307/50000000000000 : ℝ)^3771 := by
    have hnat : (627179107 : ℕ)^4795*50000000000000^3771 ≤ 11443808717307^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627179107 2000000000 11443808717307 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112035377/10000000000 : ℝ), (2659401823/5000000000 : ℝ), (627179107/2000000000 : ℝ)] ![(32303941728469/100000000000000 : ℝ), (22404220414191/50000000000000 : ℝ), (11443808717307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112035377/10000000000 : ℝ)|^4795 ≤ (32303941728469/100000000000000 : ℝ)^3771
        have hw : |(4112035377/10000000000 : ℝ)|=(4112035377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2659401823/5000000000 : ℝ)|^4795 ≤ (22404220414191/50000000000000 : ℝ)^3771
        have hw : |(2659401823/5000000000 : ℝ)|=(2659401823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627179107/2000000000 : ℝ)|^4795 ≤ (11443808717307/50000000000000 : ℝ)^3771
        have hw : |(627179107/2000000000 : ℝ)|=(627179107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1619_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (527/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24037/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4791/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4791 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4791*1^1024 ≤ 0^1024*1^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4791/1024 : ℝ) ≤ (687264218123133633/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4791 ≤ (687264218123133633/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4791*50000000000000000000^1024 ≤ 687264218123133633^1024*5^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 687264218123133633 50000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (687264218123133633/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4791 := by
      have hnat : (1 : ℕ)^1024*1^4791 ≤ 1^4791*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50687264218123133633/50000000000000000000 : ℝ) ≤ (2005844178427953/2000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (50687264218123133633/50000000000000000000 : ℝ)^1024 ≤ (2005844178427953/2000000000000000 : ℝ)^4791 := by
      have hnat : (50687264218123133633 : ℕ)^1024*2000000000000000^4791 ≤ 2005844178427953^4791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50687264218123133633 50000000000000000000 2005844178427953 2000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005844178427953/2000000000000000 : ℝ)) (X := (50687264218123133633/50000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25687264218123133633/25000000000000000000 : ℝ) ≤ (1005844178427953/1000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (25687264218123133633/25000000000000000000 : ℝ)^1024 ≤ (1005844178427953/1000000000000000 : ℝ)^4791 := by
      have hnat : (25687264218123133633 : ℕ)^1024*1000000000000000^4791 ≤ 1005844178427953^4791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25687264218123133633 25000000000000000000 1005844178427953 1000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005844178427953/1000000000000000 : ℝ)) (X := (25687264218123133633/25000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5844178427953/800000000000000 : ℝ)*(0 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5844178427953/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(687264218123133633/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5844178427953/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4791/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5844178427953/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2005844178427953/2000000000000000 : ℝ) by norm_num, show 1+(687264218123133633/50000000000000000000 : ℝ)+(0 : ℝ)=(50687264218123133633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(687264218123133633/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5844178427953/800000000000000 : ℝ)*(2/5 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5844178427953/800000000000000 : ℝ)*(2/5 : ℝ)=(1005844178427953/1000000000000000 : ℝ) by norm_num, show 1+2*(687264218123133633/50000000000000000000 : ℝ)=(25687264218123133633/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5844178427953/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5844178427953/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5844178427953/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5844178427953/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5844178427953/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5844178427953/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-309729537/2000000000 : ℝ)*X 0 0+(116501119/200000000 : ℝ)*X 0 1+(4899679261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5450022781/10000000000 : ℝ)*X 1 0+(-2059973559/10000000000 : ℝ)*X 1 1+(195987173/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((218000903/400000000 : ℝ)*X 2 0+(4899679359/10000000000 : ℝ)*X 2 1+(-257496723/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((164215509/400000000 : ℝ)*X 0 0+(3075855749/10000000000 : ℝ)*X 0 1+(1075359049/2000000000 : ℝ)*X 0 2+(164215509/400000000 : ℝ)*X 1 0+(3075855749/10000000000 : ℝ)*X 1 1+(1075359049/2000000000 : ℝ)*X 1 2+(164215509/400000000 : ℝ)*X 2 0+(3075855749/10000000000 : ℝ)*X 2 1+(1075359049/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-310264321/2000000000 : ℝ)*X 0 0+(4923001319/10000000000 : ℝ)*X 0 1+(290045487/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197317957/10000000000 : ℝ)*X 1 0+(-1158743291/10000000000 : ℝ)*X 1 1+(1450227443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197317949/10000000000 : ℝ)*X 2 0+(2900455127/5000000000 : ℝ)*X 2 1+(-579371279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4112035377/10000000000 : ℝ)*X 0 0+(2659401823/5000000000 : ℝ)*X 0 1+(627179107/2000000000 : ℝ)*X 0 2+(4112035377/10000000000 : ℝ)*X 1 0+(2659401823/5000000000 : ℝ)*X 1 1+(627179107/2000000000 : ℝ)*X 1 2+(4112035377/10000000000 : ℝ)*X 2 0+(2659401823/5000000000 : ℝ)*X 2 1+(627179107/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126315611609532632729607/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162918451/25000000000000 : ℝ)*(base19) + (558417757/100000000000000 : ℝ)*(base23) + (9665941/6250000000000 : ℝ)*(upper3) + (3570433/12500000000000 : ℝ)*(upper4) + (28006699/100000000000000 : ℝ)*(upper5) + (757626729858173/100000000000000 : ℝ)*(major0) + (757626729858173/100000000000000 : ℝ)*(major1) + (757626729858173/100000000000000 : ℝ)*(major2) + (1080643848124729/100000000000000 : ℝ)*(sp0) + (135080655644597/12500000000000 : ℝ)*(sp1) + (540322669206411/50000000000000 : ℝ)*(sp2) + (434606053530939/100000000000000 : ℝ)*(sp3) + (40974117/2000000000000 : ℝ)*(sp4) + (140409181/10000000000000 : ℝ)*(sp7) + (434607457622749/100000000000000 : ℝ)*(f.failure) + (54032294841529/5000000000000 : ℝ)*(f.sum) + (74401992490131/40000000000000000000000000000 : ℝ)*base66 + (460420887029869/80000000000000000000000000000 : ℝ)*base67 + (55684425210131/80000000000000000000000000000 : ℝ)*base70 + (231974227370131/80000000000000000000000000000 : ℝ)*base72 + (211706917229869/40000000000000000000000000000 : ℝ)*base73 + (349150979690131/80000000000000000000000000000 : ℝ)*base76 + (131790365109869/80000000000000000000000000000 : ℝ)*base77 + (222201895189869/80000000000000000000000000000 : ℝ)*base79 + (70118009570131/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (26207937/5000000000000000000000 : ℝ)*base90 + (26207937/5000000000000000000000 : ℝ)*base92 + (26207937/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (338796189132360419119581/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103410379/6250000000000 : ℝ)*(base19) + (1965237001/100000000000000 : ℝ)*(base23) + (38837633/12500000000000 : ℝ)*(base39) + (8082417/4000000000000 : ℝ)*(upper3) + (39128029/10000000000000 : ℝ)*(upper5) + (798586826315223/100000000000000 : ℝ)*(major0) + (798586826315223/100000000000000 : ℝ)*(major1) + (798586515614159/100000000000000 : ℝ)*(major2) + (2753745263/50000000000000 : ℝ)*(sp1) + (5632753197/100000000000000 : ℝ)*(sp2) + (56953455961579/5000000000000 : ℝ)*(sp4) + (1139061957174989/100000000000000 : ℝ)*(sp5) + (569530915971223/50000000000000 : ℝ)*(sp6) + (458103940367641/100000000000000 : ℝ)*(sp7) + (458103940367641/100000000000000 : ℝ)*(f.failure) + (284767357483161/25000000000000 : ℝ)*(f.sum) + (37511639872477/40000000000000000000000000000 : ℝ)*base66 + (151380920293473/80000000000000000000000000000 : ℝ)*base68 + (42766001828519/80000000000000000000000000000 : ℝ)*base69 + (312378053306527/80000000000000000000000000000 : ℝ)*base71 + (60940379712477/40000000000000000000000000000 : ℝ)*base74 + (175399741188519/80000000000000000000000000000 : ℝ)*base75 + (113573922251481/80000000000000000000000000000 : ℝ)*base78 + (240805914811481/80000000000000000000000000000 : ℝ)*base80 + (150548627868519/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (23590867/5000000000000000000000 : ℝ)*base89 + (23590867/5000000000000000000000 : ℝ)*base91 + (23590867/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1619_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (527/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24037/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1619_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1619_s1_0 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1667933921/10000000000 : ℝ)*x 0 + (5521668981/10000000000 : ℝ)*x 1 + (1281458633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1667933921/10000000000 : ℝ)^4795 ≤ (2563920874983/25000000000000 : ℝ)^3771 := by
    have hnat : (1667933921 : ℕ)^4795*25000000000000^3771 ≤ 2563920874983^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667933921 10000000000 2563920874983 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5521668981/10000000000 : ℝ)^4795 ≤ (4699272237399/10000000000000 : ℝ)^3771 := by
    have hnat : (5521668981 : ℕ)^4795*10000000000000^3771 ≤ 4699272237399^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521668981 10000000000 4699272237399 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281458633/2500000000 : ℝ)^4795 ≤ (21375797056221/50000000000000 : ℝ)^3771 := by
    have hnat : (1281458633 : ℕ)^4795*50000000000000^3771 ≤ 21375797056221^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281458633 2500000000 21375797056221 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1667933921/10000000000 : ℝ), (5521668981/10000000000 : ℝ), (1281458633/2500000000 : ℝ)] ![(2563920874983/25000000000000 : ℝ), (4699272237399/10000000000000 : ℝ), (21375797056221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1667933921/10000000000 : ℝ)|^4795 ≤ (2563920874983/25000000000000 : ℝ)^3771
        have hw : |(-1667933921/10000000000 : ℝ)|=(1667933921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5521668981/10000000000 : ℝ)|^4795 ≤ (4699272237399/10000000000000 : ℝ)^3771
        have hw : |(5521668981/10000000000 : ℝ)|=(5521668981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1281458633/2500000000 : ℝ)|^4795 ≤ (21375797056221/50000000000000 : ℝ)^3771
        have hw : |(1281458633/2500000000 : ℝ)|=(1281458633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s1_1 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369309249/10000000000 : ℝ)*x 0 + (-46866111/250000000 : ℝ)*x 1 + (2562917173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369309249/10000000000 : ℝ)^4795 ≤ (45350161971381/100000000000000 : ℝ)^3771 := by
    have hnat : (5369309249 : ℕ)^4795*100000000000000^3771 ≤ 45350161971381^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369309249 10000000000 45350161971381 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46866111/250000000 : ℝ)^4795 ≤ (11898245877673/100000000000000 : ℝ)^3771 := by
    have hnat : (46866111 : ℕ)^4795*100000000000000^3771 ≤ 11898245877673^3771*250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46866111 250000000 11898245877673 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2562917173/5000000000 : ℝ)^4795 ≤ (4275159213987/10000000000000 : ℝ)^3771 := by
    have hnat : (2562917173 : ℕ)^4795*10000000000000^3771 ≤ 4275159213987^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562917173 5000000000 4275159213987 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369309249/10000000000 : ℝ), (-46866111/250000000 : ℝ), (2562917173/5000000000 : ℝ)] ![(45350161971381/100000000000000 : ℝ), (11898245877673/100000000000000 : ℝ), (4275159213987/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369309249/10000000000 : ℝ)|^4795 ≤ (45350161971381/100000000000000 : ℝ)^3771
        have hw : |(5369309249/10000000000 : ℝ)|=(5369309249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46866111/250000000 : ℝ)|^4795 ≤ (11898245877673/100000000000000 : ℝ)^3771
        have hw : |(-46866111/250000000 : ℝ)|=(46866111/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2562917173/5000000000 : ℝ)|^4795 ≤ (4275159213987/10000000000000 : ℝ)^3771
        have hw : |(2562917173/5000000000 : ℝ)|=(2562917173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s1_2 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536930937/1000000000 : ℝ)*x 0 + (128145853/250000000 : ℝ)*x 1 + (-58582643/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536930937/1000000000 : ℝ)^4795 ≤ (9070032654177/20000000000000 : ℝ)^3771 := by
    have hnat : (536930937 : ℕ)^4795*20000000000000^3771 ≤ 9070032654177^3771*1000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536930937 1000000000 9070032654177 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128145853/250000000 : ℝ)^4795 ≤ (4275158974309/10000000000000 : ℝ)^3771 := by
    have hnat : (128145853 : ℕ)^4795*10000000000000^3771 ≤ 4275158974309^3771*250000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128145853 250000000 4275158974309 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58582643/312500000 : ℝ)^4795 ≤ (47592987901/400000000000 : ℝ)^3771 := by
    have hnat : (58582643 : ℕ)^4795*400000000000^3771 ≤ 47592987901^3771*312500000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58582643 312500000 47592987901 400000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536930937/1000000000 : ℝ), (128145853/250000000 : ℝ), (-58582643/312500000 : ℝ)] ![(9070032654177/20000000000000 : ℝ), (4275158974309/10000000000000 : ℝ), (47592987901/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536930937/1000000000 : ℝ)|^4795 ≤ (9070032654177/20000000000000 : ℝ)^3771
        have hw : |(536930937/1000000000 : ℝ)|=(536930937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128145853/250000000 : ℝ)|^4795 ≤ (4275158974309/10000000000000 : ℝ)^3771
        have hw : |(128145853/250000000 : ℝ)|=(128145853/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58582643/312500000 : ℝ)|^4795 ≤ (47592987901/400000000000 : ℝ)^3771
        have hw : |(-58582643/312500000 : ℝ)|=(58582643/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s1_3 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048738311/2500000000 : ℝ)*x 0 + (3724697107/10000000000 : ℝ)*x 1 + (4708935639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048738311/2500000000 : ℝ)^4795 ≤ (2070905103491/6250000000000 : ℝ)^3771 := by
    have hnat : (1048738311 : ℕ)^4795*6250000000000^3771 ≤ 2070905103491^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048738311 2500000000 2070905103491 6250000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3724697107/10000000000 : ℝ)^4795 ≤ (28485406670203/100000000000000 : ℝ)^3771 := by
    have hnat : (3724697107 : ℕ)^4795*100000000000000^3771 ≤ 28485406670203^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724697107 10000000000 28485406670203 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4708935639/10000000000 : ℝ)^4795 ≤ (7676022333531/20000000000000 : ℝ)^3771 := by
    have hnat : (4708935639 : ℕ)^4795*20000000000000^3771 ≤ 7676022333531^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4708935639 10000000000 7676022333531 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048738311/2500000000 : ℝ), (3724697107/10000000000 : ℝ), (4708935639/10000000000 : ℝ)] ![(2070905103491/6250000000000 : ℝ), (28485406670203/100000000000000 : ℝ), (7676022333531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048738311/2500000000 : ℝ)|^4795 ≤ (2070905103491/6250000000000 : ℝ)^3771
        have hw : |(1048738311/2500000000 : ℝ)|=(1048738311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3724697107/10000000000 : ℝ)|^4795 ≤ (28485406670203/100000000000000 : ℝ)^3771
        have hw : |(3724697107/10000000000 : ℝ)|=(3724697107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4708935639/10000000000 : ℝ)|^4795 ≤ (7676022333531/20000000000000 : ℝ)^3771
        have hw : |(4708935639/10000000000 : ℝ)|=(4708935639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s1_4 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104258683/625000000 : ℝ)*x 0 + (5130070023/10000000000 : ℝ)*x 1 + (110347383/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104258683/625000000 : ℝ)^4795 ≤ (2564321588317/25000000000000 : ℝ)^3771 := by
    have hnat : (104258683 : ℕ)^4795*25000000000000^3771 ≤ 2564321588317^3771*625000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104258683 625000000 2564321588317 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130070023/10000000000 : ℝ)^4795 ≤ (8559303495573/20000000000000 : ℝ)^3771 := by
    have hnat : (5130070023 : ℕ)^4795*20000000000000^3771 ≤ 8559303495573^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130070023 10000000000 8559303495573 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110347383/200000000 : ℝ)^4795 ≤ (4694619615349/10000000000000 : ℝ)^3771 := by
    have hnat : (110347383 : ℕ)^4795*10000000000000^3771 ≤ 4694619615349^3771*200000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110347383 200000000 4694619615349 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104258683/625000000 : ℝ), (5130070023/10000000000 : ℝ), (110347383/200000000 : ℝ)] ![(2564321588317/25000000000000 : ℝ), (8559303495573/20000000000000 : ℝ), (4694619615349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104258683/625000000 : ℝ)|^4795 ≤ (2564321588317/25000000000000 : ℝ)^3771
        have hw : |(-104258683/625000000 : ℝ)|=(104258683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130070023/10000000000 : ℝ)|^4795 ≤ (8559303495573/20000000000000 : ℝ)^3771
        have hw : |(5130070023/10000000000 : ℝ)|=(5130070023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110347383/200000000 : ℝ)|^4795 ≤ (4694619615349/10000000000000 : ℝ)^3771
        have hw : |(110347383/200000000 : ℝ)|=(110347383/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s1_5 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631934383/5000000000 : ℝ)*x 0 + (-370777267/2500000000 : ℝ)*x 1 + (5517369489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631934383/5000000000 : ℝ)^4795 ≤ (44220795687509/100000000000000 : ℝ)^3771 := by
    have hnat : (2631934383 : ℕ)^4795*100000000000000^3771 ≤ 44220795687509^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631934383 5000000000 44220795687509 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370777267/2500000000 : ℝ)^4795 ≤ (552062780071/6250000000000 : ℝ)^3771 := by
    have hnat : (370777267 : ℕ)^4795*6250000000000^3771 ≤ 552062780071^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370777267 2500000000 552062780071 6250000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517369489/10000000000 : ℝ)^4795 ≤ (11736549955311/25000000000000 : ℝ)^3771 := by
    have hnat : (5517369489 : ℕ)^4795*25000000000000^3771 ≤ 11736549955311^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517369489 10000000000 11736549955311 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631934383/5000000000 : ℝ), (-370777267/2500000000 : ℝ), (5517369489/10000000000 : ℝ)] ![(44220795687509/100000000000000 : ℝ), (552062780071/6250000000000 : ℝ), (11736549955311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631934383/5000000000 : ℝ)|^4795 ≤ (44220795687509/100000000000000 : ℝ)^3771
        have hw : |(2631934383/5000000000 : ℝ)|=(2631934383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-370777267/2500000000 : ℝ)|^4795 ≤ (552062780071/6250000000000 : ℝ)^3771
        have hw : |(-370777267/2500000000 : ℝ)|=(370777267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517369489/10000000000 : ℝ)|^4795 ≤ (11736549955311/25000000000000 : ℝ)^3771
        have hw : |(5517369489/10000000000 : ℝ)|=(5517369489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s1_6 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315967029/2500000000 : ℝ)*x 0 + (2758684867/5000000000 : ℝ)*x 1 + (-296621927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315967029/2500000000 : ℝ)^4795 ≤ (44220788744193/100000000000000 : ℝ)^3771 := by
    have hnat : (1315967029 : ℕ)^4795*100000000000000^3771 ≤ 44220788744193^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315967029 2500000000 44220788744193 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758684867/5000000000 : ℝ)^4795 ≤ (2347310123599/5000000000000 : ℝ)^3771 := by
    have hnat : (2758684867 : ℕ)^4795*5000000000000^3771 ≤ 2347310123599^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758684867 5000000000 2347310123599 5000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296621927/2000000000 : ℝ)^4795 ≤ (4416504387511/50000000000000 : ℝ)^3771 := by
    have hnat : (296621927 : ℕ)^4795*50000000000000^3771 ≤ 4416504387511^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296621927 2000000000 4416504387511 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315967029/2500000000 : ℝ), (2758684867/5000000000 : ℝ), (-296621927/2000000000 : ℝ)] ![(44220788744193/100000000000000 : ℝ), (2347310123599/5000000000000 : ℝ), (4416504387511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315967029/2500000000 : ℝ)|^4795 ≤ (44220788744193/100000000000000 : ℝ)^3771
        have hw : |(1315967029/2500000000 : ℝ)|=(1315967029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758684867/5000000000 : ℝ)|^4795 ≤ (2347310123599/5000000000000 : ℝ)^3771
        have hw : |(2758684867/5000000000 : ℝ)|=(2758684867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-296621927/2000000000 : ℝ)|^4795 ≤ (4416504387511/50000000000000 : ℝ)^3771
        have hw : |(-296621927/2000000000 : ℝ)|=(296621927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s1_7 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4195461073/10000000000 : ℝ)*x 0 + (4698405251/10000000000 : ℝ)*x 1 + (933846927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195461073/10000000000 : ℝ)^4795 ≤ (8284895530213/25000000000000 : ℝ)^3771 := by
    have hnat : (4195461073 : ℕ)^4795*25000000000000^3771 ≤ 8284895530213^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195461073 10000000000 8284895530213 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4698405251/10000000000 : ℝ)^4795 ≤ (9567752714207/25000000000000 : ℝ)^3771 := by
    have hnat : (4698405251 : ℕ)^4795*25000000000000^3771 ≤ 9567752714207^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698405251 10000000000 9567752714207 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933846927/2500000000 : ℝ)^4795 ≤ (28589407008969/100000000000000 : ℝ)^3771 := by
    have hnat : (933846927 : ℕ)^4795*100000000000000^3771 ≤ 28589407008969^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933846927 2500000000 28589407008969 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195461073/10000000000 : ℝ), (4698405251/10000000000 : ℝ), (933846927/2500000000 : ℝ)] ![(8284895530213/25000000000000 : ℝ), (9567752714207/25000000000000 : ℝ), (28589407008969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195461073/10000000000 : ℝ)|^4795 ≤ (8284895530213/25000000000000 : ℝ)^3771
        have hw : |(4195461073/10000000000 : ℝ)|=(4195461073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4698405251/10000000000 : ℝ)|^4795 ≤ (9567752714207/25000000000000 : ℝ)^3771
        have hw : |(4698405251/10000000000 : ℝ)|=(4698405251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933846927/2500000000 : ℝ)|^4795 ≤ (28589407008969/100000000000000 : ℝ)^3771
        have hw : |(933846927/2500000000 : ℝ)|=(933846927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1619_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (527/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9287/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (221/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (527/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (527/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (527/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (527/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (527/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (527/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (527/12500 : ℝ) ^ (4791/1024 : ℝ) ≤ (1841948196141/5000000000000000000 : ℝ) := by
    have hpowers : (527/12500 : ℝ)^4791 ≤ (1841948196141/5000000000000000000 : ℝ)^1024 := by
      have hnat : (527 : ℕ)^4791*5000000000000000000^1024 ≤ 1841948196141^1024*12500^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        527 12500 1841948196141 5000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (527/12500 : ℝ)) (X := (1841948196141/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24037/100000 : ℝ) ^ (4791/1024 : ℝ) ≤ (126857958194374391/100000000000000000000 : ℝ) := by
    have hpowers : (24037/100000 : ℝ)^4791 ≤ (126857958194374391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24037 : ℕ)^4791*100000000000000000000^1024 ≤ 126857958194374391^1024*100000^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24037 100000 126857958194374391 100000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24037/100000 : ℝ)) (X := (126857958194374391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500001841948196141/2500000000000000000 : ℝ) ≤ (1250000196843499/1250000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (2500001841948196141/2500000000000000000 : ℝ)^1024 ≤ (1250000196843499/1250000000000000 : ℝ)^4791 := by
      have hnat : (2500001841948196141 : ℕ)^1024*1250000000000000^4791 ≤ 1250000196843499^4791*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500001841948196141 2500000000000000000 1250000196843499 1250000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000196843499/1250000000000000 : ℝ)) (X := (2500001841948196141/2500000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100126894797158297211/100000000000000000000 : ℝ) ≤ (2500677705586179/2500000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (100126894797158297211/100000000000000000000 : ℝ)^1024 ≤ (2500677705586179/2500000000000000 : ℝ)^4791 := by
      have hnat : (100126894797158297211 : ℕ)^1024*2500000000000000^4791 ≤ 2500677705586179^4791*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100126894797158297211 100000000000000000000 2500677705586179 2500000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500677705586179/2500000000000000 : ℝ)) (X := (100126894797158297211/100000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50126857958194374391/50000000000000000000 : ℝ) ≤ (31266937718567/31250000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (50126857958194374391/50000000000000000000 : ℝ)^1024 ≤ (31266937718567/31250000000000 : ℝ)^4791 := by
      have hnat : (50126857958194374391 : ℕ)^1024*31250000000000^4791 ≤ 31266937718567^4791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50126857958194374391 50000000000000000000 31266937718567 31250000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31266937718567/31250000000000 : ℝ)) (X := (50126857958194374391/50000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1841948196141/5000000000000000000 : ℝ) ≤ ((24773398354668046583/24776250000000000000 : ℝ)+2*(677311899181/495525000000000 : ℝ)*(527/12500 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (24773398354668046583/24776250000000000000 : ℝ)+2*(677311899181/495525000000000 : ℝ)*(527/12500 : ℝ)=(1250000196843499/1250000000000000 : ℝ) by norm_num, show 1+2*(1841948196141/5000000000000000000 : ℝ)=(2500001841948196141/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(126857958194374391/100000000000000000000 : ℝ)+(1841948196141/5000000000000000000 : ℝ) ≤ ((24773398354668046583/24776250000000000000 : ℝ)+(677311899181/495525000000000 : ℝ)*((24037/100000 : ℝ)+(527/12500 : ℝ)))^(4791/1024 : ℝ) := by
    rw [show (24773398354668046583/24776250000000000000 : ℝ)+(677311899181/495525000000000 : ℝ)*((24037/100000 : ℝ)+(527/12500 : ℝ))=(2500677705586179/2500000000000000 : ℝ) by norm_num, show 1+(126857958194374391/100000000000000000000 : ℝ)+(1841948196141/5000000000000000000 : ℝ)=(100126894797158297211/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(126857958194374391/100000000000000000000 : ℝ) ≤ ((24773398354668046583/24776250000000000000 : ℝ)+2*(677311899181/495525000000000 : ℝ)*(24037/100000 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (24773398354668046583/24776250000000000000 : ℝ)+2*(677311899181/495525000000000 : ℝ)*(24037/100000 : ℝ)=(31266937718567/31250000000000 : ℝ) by norm_num, show 1+2*(126857958194374391/100000000000000000000 : ℝ)=(50126857958194374391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24773398354668046583/24776250000000000000 : ℝ)*(X 1 0+X 2 0)+(677311899181/495525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (527/12500 : ℝ)) (hi := (24037/100000 : ℝ)) (c := (24773398354668046583/24776250000000000000 : ℝ)) (alpha := (677311899181/495525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24773398354668046583/24776250000000000000 : ℝ)*(X 0 1+X 2 1)+(677311899181/495525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (527/12500 : ℝ)) (hi := (24037/100000 : ℝ)) (c := (24773398354668046583/24776250000000000000 : ℝ)) (alpha := (677311899181/495525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24773398354668046583/24776250000000000000 : ℝ)*(X 0 2+X 1 2)+(677311899181/495525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (527/12500 : ℝ)) (hi := (24037/100000 : ℝ)) (c := (24773398354668046583/24776250000000000000 : ℝ)) (alpha := (677311899181/495525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1667933921/10000000000 : ℝ)*X 0 0+(5521668981/10000000000 : ℝ)*X 0 1+(1281458633/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369309249/10000000000 : ℝ)*X 1 0+(-46866111/250000000 : ℝ)*X 1 1+(2562917173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536930937/1000000000 : ℝ)*X 2 0+(128145853/250000000 : ℝ)*X 2 1+(-58582643/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048738311/2500000000 : ℝ)*X 0 0+(3724697107/10000000000 : ℝ)*X 0 1+(4708935639/10000000000 : ℝ)*X 0 2+(1048738311/2500000000 : ℝ)*X 1 0+(3724697107/10000000000 : ℝ)*X 1 1+(4708935639/10000000000 : ℝ)*X 1 2+(1048738311/2500000000 : ℝ)*X 2 0+(3724697107/10000000000 : ℝ)*X 2 1+(4708935639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104258683/625000000 : ℝ)*X 0 0+(5130070023/10000000000 : ℝ)*X 0 1+(110347383/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2631934383/5000000000 : ℝ)*X 1 0+(-370777267/2500000000 : ℝ)*X 1 1+(5517369489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315967029/2500000000 : ℝ)*X 2 0+(2758684867/5000000000 : ℝ)*X 2 1+(-296621927/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4195461073/10000000000 : ℝ)*X 0 0+(4698405251/10000000000 : ℝ)*X 0 1+(933846927/2500000000 : ℝ)*X 0 2+(4195461073/10000000000 : ℝ)*X 1 0+(4698405251/10000000000 : ℝ)*X 1 1+(933846927/2500000000 : ℝ)*X 1 2+(4195461073/10000000000 : ℝ)*X 2 0+(4698405251/10000000000 : ℝ)*X 2 1+(933846927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1413976498100822872210842617/206468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130237679/50000000000000 : ℝ)*(base1) + (1316469469/100000000000000 : ℝ)*(base19) + (137340137/10000000000000 : ℝ)*(base23) + (45498851/25000000000000 : ℝ)*(upper3) + (112184307/100000000000000 : ℝ)*(upper5) + (1771172437017601/100000000000000 : ℝ)*(major0) + (1771172437017601/100000000000000 : ℝ)*(major1) + (1771172437017601/100000000000000 : ℝ)*(major2) + (1263158333832387/50000000000000 : ℝ)*(sp0) + (252632222083393/10000000000000 : ℝ)*(sp1) + (252632216390203/10000000000000 : ℝ)*(sp2) + (508008542070527/50000000000000 : ℝ)*(sp3) + (111408031/1562500000000 : ℝ)*(sp4) + (3763836041/100000000000000 : ℝ)*(sp7) + (508010554226227/50000000000000 : ℝ)*(f.failure) + (12631617686517/500000000000 : ℝ)*(f.sum) + (260378671270009/99105000000000000000000000000 : ℝ)*base65 + (23290908951811082383/2477625000000000000000000000000000 : ℝ)*base67 + (27376963734980207383/2477625000000000000000000000000000 : ℝ)*base69 + (29502882837208082383/2477625000000000000000000000000000 : ℝ)*base71 + (566465483956879/99105000000000000000000000000 : ℝ)*base73 + (8839892765448707383/2477625000000000000000000000000000 : ℝ)*base75 + (18108279193816832383/2477625000000000000000000000000000 : ℝ)*base77 + (290101731358167617/2477625000000000000000000000000000 : ℝ)*base80 + (257753570688227/49552500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13078449/2500000000000000000000 : ℝ)*base89 + (13078449/2500000000000000000000 : ℝ)*base91 + (13078449/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (736632944202227624213352843/103234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73581527/5000000000000 : ℝ)*(base19) + (244370471/20000000000000 : ℝ)*(base23) + (10601587/25000000000000 : ℝ)*(upper2) + (39129823/12500000000000 : ℝ)*(upper3) + (53243019/100000000000000 : ℝ)*(upper5) + (113136922834613/6250000000000 : ℝ)*(major0) + (113136922834613/6250000000000 : ℝ)*(major1) + (113136922834613/6250000000000 : ℝ)*(major2) + (11088865467/100000000000000 : ℝ)*(sp1) + (10514261399/100000000000000 : ℝ)*(sp2) + (645494395957367/25000000000000 : ℝ)*(sp4) + (1290982511666731/50000000000000 : ℝ)*(sp5) + (1290982923857857/50000000000000 : ℝ)*(sp6) + (1038403709026833/100000000000000 : ℝ)*(sp7) + (1038403709026833/100000000000000 : ℝ)*(f.failure) + (645494395957367/25000000000000 : ℝ)*(f.sum) + (108813309628033/99105000000000000000000000000 : ℝ)*base66 + (1435062576451182883/309703125000000000000000000000000 : ℝ)*base67 + (266194247428271129/154851562500000000000000000000000 : ℝ)*base69 + (296538491964052379/154851562500000000000000000000000 : ℝ)*base71 + (100509167327357/99105000000000000000000000000 : ℝ)*base73 + (323588693800927379/154851562500000000000000000000000 : ℝ)*base75 + (5433992338442117/309703125000000000000000000000000 : ℝ)*base78 + (2759942754238182883/309703125000000000000000000000000 : ℝ)*base79 + (178035238846379/49552500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5963771/5000000000000000000000 : ℝ)*base89 + (5963771/5000000000000000000000 : ℝ)*base91 + (5963771/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1619_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (527/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (221/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1619_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1619_s2_0 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1680650191/10000000000 : ℝ)*x 0 + (5462937617/10000000000 : ℝ)*x 1 + (323514127/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1680650191/10000000000 : ℝ)^4795 ≤ (2071041420017/20000000000000 : ℝ)^3771 := by
    have hnat : (1680650191 : ℕ)^4795*20000000000000^3771 ≤ 2071041420017^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680650191 10000000000 2071041420017 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462937617/10000000000 : ℝ)^4795 ≤ (23179037028009/50000000000000 : ℝ)^3771 := by
    have hnat : (5462937617 : ℕ)^4795*50000000000000^3771 ≤ 23179037028009^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462937617 10000000000 23179037028009 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323514127/625000000 : ℝ)^4795 ≤ (21643359417819/50000000000000 : ℝ)^3771 := by
    have hnat : (323514127 : ℕ)^4795*50000000000000^3771 ≤ 21643359417819^3771*625000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323514127 625000000 21643359417819 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1680650191/10000000000 : ℝ), (5462937617/10000000000 : ℝ), (323514127/625000000 : ℝ)] ![(2071041420017/20000000000000 : ℝ), (23179037028009/50000000000000 : ℝ), (21643359417819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1680650191/10000000000 : ℝ)|^4795 ≤ (2071041420017/20000000000000 : ℝ)^3771
        have hw : |(-1680650191/10000000000 : ℝ)|=(1680650191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462937617/10000000000 : ℝ)|^4795 ≤ (23179037028009/50000000000000 : ℝ)^3771
        have hw : |(5462937617/10000000000 : ℝ)|=(5462937617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323514127/625000000 : ℝ)|^4795 ≤ (21643359417819/50000000000000 : ℝ)^3771
        have hw : |(323514127/625000000 : ℝ)|=(323514127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s2_1 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338486283/2500000000 : ℝ)*x 0 + (-1828620631/10000000000 : ℝ)*x 1 + (5176226143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338486283/2500000000 : ℝ)^4795 ≤ (22592609990483/50000000000000 : ℝ)^3771 := by
    have hnat : (1338486283 : ℕ)^4795*50000000000000^3771 ≤ 22592609990483^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338486283 2500000000 22592609990483 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1828620631/10000000000 : ℝ)^4795 ≤ (5764029995923/50000000000000 : ℝ)^3771 := by
    have hnat : (1828620631 : ℕ)^4795*50000000000000^3771 ≤ 5764029995923^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828620631 10000000000 5764029995923 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176226143/10000000000 : ℝ)^4795 ≤ (43286720015949/100000000000000 : ℝ)^3771 := by
    have hnat : (5176226143 : ℕ)^4795*100000000000000^3771 ≤ 43286720015949^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176226143 10000000000 43286720015949 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338486283/2500000000 : ℝ), (-1828620631/10000000000 : ℝ), (5176226143/10000000000 : ℝ)] ![(22592609990483/50000000000000 : ℝ), (5764029995923/50000000000000 : ℝ), (43286720015949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338486283/2500000000 : ℝ)|^4795 ≤ (22592609990483/50000000000000 : ℝ)^3771
        have hw : |(1338486283/2500000000 : ℝ)|=(1338486283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1828620631/10000000000 : ℝ)|^4795 ≤ (5764029995923/50000000000000 : ℝ)^3771
        have hw : |(-1828620631/10000000000 : ℝ)|=(1828620631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176226143/10000000000 : ℝ)|^4795 ≤ (43286720015949/100000000000000 : ℝ)^3771
        have hw : |(5176226143/10000000000 : ℝ)|=(5176226143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s2_2 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167310789/312500000 : ℝ)*x 0 + (5176225939/10000000000 : ℝ)*x 1 + (-365724149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167310789/312500000 : ℝ)^4795 ≤ (45185221225803/100000000000000 : ℝ)^3771 := by
    have hnat : (167310789 : ℕ)^4795*100000000000000^3771 ≤ 45185221225803^3771*312500000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167310789 312500000 45185221225803 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176225939/10000000000 : ℝ)^4795 ≤ (43286717846729/100000000000000 : ℝ)^3771 := by
    have hnat : (5176225939 : ℕ)^4795*100000000000000^3771 ≤ 43286717846729^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176225939 10000000000 43286717846729 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365724149/2000000000 : ℝ)^4795 ≤ (2305612181137/20000000000000 : ℝ)^3771 := by
    have hnat : (365724149 : ℕ)^4795*20000000000000^3771 ≤ 2305612181137^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365724149 2000000000 2305612181137 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167310789/312500000 : ℝ), (5176225939/10000000000 : ℝ), (-365724149/2000000000 : ℝ)] ![(45185221225803/100000000000000 : ℝ), (43286717846729/100000000000000 : ℝ), (2305612181137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167310789/312500000 : ℝ)|^4795 ≤ (45185221225803/100000000000000 : ℝ)^3771
        have hw : |(167310789/312500000 : ℝ)|=(167310789/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176225939/10000000000 : ℝ)|^4795 ≤ (43286717846729/100000000000000 : ℝ)^3771
        have hw : |(5176225939/10000000000 : ℝ)|=(5176225939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365724149/2000000000 : ℝ)|^4795 ≤ (2305612181137/20000000000000 : ℝ)^3771
        have hw : |(-365724149/2000000000 : ℝ)|=(365724149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s2_3 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4204358863/10000000000 : ℝ)*x 0 + (3859380373/10000000000 : ℝ)*x 1 + (4572285403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204358863/10000000000 : ℝ)^4795 ≤ (6645795148607/20000000000000 : ℝ)^3771 := by
    have hnat : (4204358863 : ℕ)^4795*20000000000000^3771 ≤ 6645795148607^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204358863 10000000000 6645795148607 20000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3859380373/10000000000 : ℝ)^4795 ≤ (14900748628281/50000000000000 : ℝ)^3771 := by
    have hnat : (3859380373 : ℕ)^4795*50000000000000^3771 ≤ 14900748628281^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3859380373 10000000000 14900748628281 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4572285403/10000000000 : ℝ)^4795 ≤ (36969526977663/100000000000000 : ℝ)^3771 := by
    have hnat : (4572285403 : ℕ)^4795*100000000000000^3771 ≤ 36969526977663^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572285403 10000000000 36969526977663 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204358863/10000000000 : ℝ), (3859380373/10000000000 : ℝ), (4572285403/10000000000 : ℝ)] ![(6645795148607/20000000000000 : ℝ), (14900748628281/50000000000000 : ℝ), (36969526977663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204358863/10000000000 : ℝ)|^4795 ≤ (6645795148607/20000000000000 : ℝ)^3771
        have hw : |(4204358863/10000000000 : ℝ)|=(4204358863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3859380373/10000000000 : ℝ)|^4795 ≤ (14900748628281/50000000000000 : ℝ)^3771
        have hw : |(3859380373/10000000000 : ℝ)|=(3859380373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4572285403/10000000000 : ℝ)|^4795 ≤ (36969526977663/100000000000000 : ℝ)^3771
        have hw : |(4572285403/10000000000 : ℝ)|=(4572285403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s2_4 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-840364011/5000000000 : ℝ)*x 0 + (1035691001/2000000000 : ℝ)*x 1 + (546068427/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840364011/5000000000 : ℝ)^4795 ≤ (10355816874053/100000000000000 : ℝ)^3771 := by
    have hnat : (840364011 : ℕ)^4795*100000000000000^3771 ≤ 10355816874053^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840364011 5000000000 10355816874053 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035691001/2000000000 : ℝ)^4795 ≤ (433104218571/1000000000000 : ℝ)^3771 := by
    have hnat : (1035691001 : ℕ)^4795*1000000000000^3771 ≤ 433104218571^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035691001 2000000000 433104218571 1000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546068427/1000000000 : ℝ)^4795 ≤ (11583440314069/25000000000000 : ℝ)^3771 := by
    have hnat : (546068427 : ℕ)^4795*25000000000000^3771 ≤ 11583440314069^3771*1000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546068427 1000000000 11583440314069 25000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-840364011/5000000000 : ℝ), (1035691001/2000000000 : ℝ), (546068427/1000000000 : ℝ)] ![(10355816874053/100000000000000 : ℝ), (433104218571/1000000000000 : ℝ), (11583440314069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-840364011/5000000000 : ℝ)|^4795 ≤ (10355816874053/100000000000000 : ℝ)^3771
        have hw : |(-840364011/5000000000 : ℝ)|=(840364011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035691001/2000000000 : ℝ)|^4795 ≤ (433104218571/1000000000000 : ℝ)^3771
        have hw : |(1035691001/2000000000 : ℝ)|=(1035691001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546068427/1000000000 : ℝ)|^4795 ≤ (11583440314069/25000000000000 : ℝ)^3771
        have hw : |(546068427/1000000000 : ℝ)|=(546068427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s2_5 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277674289/10000000000 : ℝ)*x 0 + (-308832461/2000000000 : ℝ)*x 1 + (5460684337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277674289/10000000000 : ℝ)^4795 ≤ (22184159552571/50000000000000 : ℝ)^3771 := by
    have hnat : (5277674289 : ℕ)^4795*50000000000000^3771 ≤ 22184159552571^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277674289 10000000000 22184159552571 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308832461/2000000000 : ℝ)^4795 ≤ (9297918907009/100000000000000 : ℝ)^3771 := by
    have hnat : (308832461 : ℕ)^4795*100000000000000^3771 ≤ 9297918907009^3771*2000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308832461 2000000000 9297918907009 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460684337/10000000000 : ℝ)^4795 ≤ (46333761979141/100000000000000 : ℝ)^3771 := by
    have hnat : (5460684337 : ℕ)^4795*100000000000000^3771 ≤ 46333761979141^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460684337 10000000000 46333761979141 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277674289/10000000000 : ℝ), (-308832461/2000000000 : ℝ), (5460684337/10000000000 : ℝ)] ![(22184159552571/50000000000000 : ℝ), (9297918907009/100000000000000 : ℝ), (46333761979141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277674289/10000000000 : ℝ)|^4795 ≤ (22184159552571/50000000000000 : ℝ)^3771
        have hw : |(5277674289/10000000000 : ℝ)|=(5277674289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-308832461/2000000000 : ℝ)|^4795 ≤ (9297918907009/100000000000000 : ℝ)^3771
        have hw : |(-308832461/2000000000 : ℝ)|=(308832461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460684337/10000000000 : ℝ)|^4795 ≤ (46333761979141/100000000000000 : ℝ)^3771
        have hw : |(5460684337/10000000000 : ℝ)|=(5460684337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s2_6 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277674559/10000000000 : ℝ)*x 0 + (2730341931/5000000000 : ℝ)*x 1 + (-386040649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277674559/10000000000 : ℝ)^4795 ≤ (2218416099567/5000000000000 : ℝ)^3771 := by
    have hnat : (5277674559 : ℕ)^4795*5000000000000^3771 ≤ 2218416099567^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277674559 10000000000 2218416099567 5000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730341931/5000000000 : ℝ)^4795 ≤ (926675137087/2000000000000 : ℝ)^3771 := by
    have hnat : (2730341931 : ℕ)^4795*2000000000000^3771 ≤ 926675137087^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730341931 5000000000 926675137087 2000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (386040649/2500000000 : ℝ)^4795 ≤ (4648960567511/50000000000000 : ℝ)^3771 := by
    have hnat : (386040649 : ℕ)^4795*50000000000000^3771 ≤ 4648960567511^3771*2500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386040649 2500000000 4648960567511 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277674559/10000000000 : ℝ), (2730341931/5000000000 : ℝ), (-386040649/2500000000 : ℝ)] ![(2218416099567/5000000000000 : ℝ), (926675137087/2000000000000 : ℝ), (4648960567511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277674559/10000000000 : ℝ)|^4795 ≤ (2218416099567/5000000000000 : ℝ)^3771
        have hw : |(5277674559/10000000000 : ℝ)|=(5277674559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730341931/5000000000 : ℝ)|^4795 ≤ (926675137087/2000000000000 : ℝ)^3771
        have hw : |(2730341931/5000000000 : ℝ)|=(2730341931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-386040649/2500000000 : ℝ)|^4795 ≤ (4648960567511/50000000000000 : ℝ)^3771
        have hw : |(-386040649/2500000000 : ℝ)|=(386040649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1619_s2_7 (p : ℝ) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210227617/500000000 : ℝ)*x 0 + (2283371607/5000000000 : ℝ)*x 1 + (3864983537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210227617/500000000 : ℝ)^4795 ≤ (3323092012379/10000000000000 : ℝ)^3771 := by
    have hnat : (210227617 : ℕ)^4795*10000000000000^3771 ≤ 3323092012379^3771*500000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210227617 500000000 3323092012379 10000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283371607/5000000000 : ℝ)^4795 ≤ (18456278078657/50000000000000 : ℝ)^3771 := by
    have hnat : (2283371607 : ℕ)^4795*50000000000000^3771 ≤ 18456278078657^3771*5000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283371607 5000000000 18456278078657 50000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3864983537/10000000000 : ℝ)^4795 ≤ (29856523704927/100000000000000 : ℝ)^3771 := by
    have hnat : (3864983537 : ℕ)^4795*100000000000000^3771 ≤ 29856523704927^3771*10000000000^4795 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3864983537 10000000000 29856523704927 100000000000000 4795 3771 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4795/1024 : ℝ)) 4795 3771 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210227617/500000000 : ℝ), (2283371607/5000000000 : ℝ), (3864983537/10000000000 : ℝ)] ![(3323092012379/10000000000000 : ℝ), (18456278078657/50000000000000 : ℝ), (29856523704927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210227617/500000000 : ℝ)|^4795 ≤ (3323092012379/10000000000000 : ℝ)^3771
        have hw : |(210227617/500000000 : ℝ)|=(210227617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2283371607/5000000000 : ℝ)|^4795 ≤ (18456278078657/50000000000000 : ℝ)^3771
        have hw : |(2283371607/5000000000 : ℝ)|=(2283371607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3864983537/10000000000 : ℝ)|^4795 ≤ (29856523704927/100000000000000 : ℝ)^3771
        have hw : |(3864983537/10000000000 : ℝ)|=(3864983537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1619_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (221/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (83/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16457/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (221/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (221/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (221/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (221/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (221/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (221/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9287/100000 : ℝ) ^ (4791/1024 : ℝ) ≤ (92654725887883/6250000000000000000 : ℝ) := by
    have hpowers : (9287/100000 : ℝ)^4791 ≤ (92654725887883/6250000000000000000 : ℝ)^1024 := by
      have hnat : (9287 : ℕ)^4791*6250000000000000000^1024 ≤ 92654725887883^1024*100000^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9287 100000 92654725887883 6250000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9287/100000 : ℝ)) (X := (92654725887883/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (221/1250 : ℝ) ^ (4791/1024 : ℝ) ≤ (15071519045962993/50000000000000000000 : ℝ) := by
    have hpowers : (221/1250 : ℝ)^4791 ≤ (15071519045962993/50000000000000000000 : ℝ)^1024 := by
      have hnat : (221 : ℕ)^4791*50000000000000000000^1024 ≤ 15071519045962993^1024*1250^4791 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        221 1250 15071519045962993 50000000000000000000 4791 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (221/1250 : ℝ)) (X := (15071519045962993/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125092654725887883/3125000000000000000 : ℝ) ≤ (5000031685187529/5000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (3125092654725887883/3125000000000000000 : ℝ)^1024 ≤ (5000031685187529/5000000000000000 : ℝ)^4791 := by
      have hnat : (3125092654725887883 : ℕ)^1024*5000000000000000^4791 ≤ 5000031685187529^4791*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125092654725887883 3125000000000000000 5000031685187529 5000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000031685187529/5000000000000000 : ℝ)) (X := (3125092654725887883/3125000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015812756853066057/50000000000000000000 : ℝ) ≤ (10000675860998011/10000000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (50015812756853066057/50000000000000000000 : ℝ)^1024 ≤ (10000675860998011/10000000000000000 : ℝ)^4791 := by
      have hnat : (50015812756853066057 : ℕ)^1024*10000000000000000^4791 ≤ 10000675860998011^4791*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015812756853066057 50000000000000000000 10000675860998011 10000000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000675860998011/10000000000000000 : ℝ)) (X := (50015812756853066057/50000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015071519045962993/25000000000000000000 : ℝ) ≤ (2500322087905241/2500000000000000 : ℝ) ^ (4791/1024 : ℝ) := by
    have hpowers : (25015071519045962993/25000000000000000000 : ℝ)^1024 ≤ (2500322087905241/2500000000000000 : ℝ)^4791 := by
      have hnat : (25015071519045962993 : ℕ)^1024*2500000000000000^4791 ≤ 2500322087905241^4791*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015071519045962993 25000000000000000000 2500322087905241 2500000000000000 1024 4791 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500322087905241/2500000000000000 : ℝ)) (X := (25015071519045962993/25000000000000000000 : ℝ)) (by norm_num) 4791 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(92654725887883/6250000000000000000 : ℝ) ≤ ((1907253533334707563/1907500000000000000 : ℝ)+2*(55680965723/76300000000000 : ℝ)*(9287/100000 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (1907253533334707563/1907500000000000000 : ℝ)+2*(55680965723/76300000000000 : ℝ)*(9287/100000 : ℝ)=(5000031685187529/5000000000000000 : ℝ) by norm_num, show 1+2*(92654725887883/6250000000000000000 : ℝ)=(3125092654725887883/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15071519045962993/50000000000000000000 : ℝ)+(92654725887883/6250000000000000000 : ℝ) ≤ ((1907253533334707563/1907500000000000000 : ℝ)+(55680965723/76300000000000 : ℝ)*((221/1250 : ℝ)+(9287/100000 : ℝ)))^(4791/1024 : ℝ) := by
    rw [show (1907253533334707563/1907500000000000000 : ℝ)+(55680965723/76300000000000 : ℝ)*((221/1250 : ℝ)+(9287/100000 : ℝ))=(10000675860998011/10000000000000000 : ℝ) by norm_num, show 1+(15071519045962993/50000000000000000000 : ℝ)+(92654725887883/6250000000000000000 : ℝ)=(50015812756853066057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15071519045962993/50000000000000000000 : ℝ) ≤ ((1907253533334707563/1907500000000000000 : ℝ)+2*(55680965723/76300000000000 : ℝ)*(221/1250 : ℝ))^(4791/1024 : ℝ) := by
    rw [show (1907253533334707563/1907500000000000000 : ℝ)+2*(55680965723/76300000000000 : ℝ)*(221/1250 : ℝ)=(2500322087905241/2500000000000000 : ℝ) by norm_num, show 1+2*(15071519045962993/50000000000000000000 : ℝ)=(25015071519045962993/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1907253533334707563/1907500000000000000 : ℝ)*(X 1 0+X 2 0)+(55680965723/76300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (9287/100000 : ℝ)) (hi := (221/1250 : ℝ)) (c := (1907253533334707563/1907500000000000000 : ℝ)) (alpha := (55680965723/76300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1907253533334707563/1907500000000000000 : ℝ)*(X 0 1+X 2 1)+(55680965723/76300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (9287/100000 : ℝ)) (hi := (221/1250 : ℝ)) (c := (1907253533334707563/1907500000000000000 : ℝ)) (alpha := (55680965723/76300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1907253533334707563/1907500000000000000 : ℝ)*(X 0 2+X 1 2)+(55680965723/76300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4791/1024 : ℝ)) (lo := (9287/100000 : ℝ)) (hi := (221/1250 : ℝ)) (c := (1907253533334707563/1907500000000000000 : ℝ)) (alpha := (55680965723/76300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1680650191/10000000000 : ℝ)*X 0 0+(5462937617/10000000000 : ℝ)*X 0 1+(323514127/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338486283/2500000000 : ℝ)*X 1 0+(-1828620631/10000000000 : ℝ)*X 1 1+(5176226143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167310789/312500000 : ℝ)*X 2 0+(5176225939/10000000000 : ℝ)*X 2 1+(-365724149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4204358863/10000000000 : ℝ)*X 0 0+(3859380373/10000000000 : ℝ)*X 0 1+(4572285403/10000000000 : ℝ)*X 0 2+(4204358863/10000000000 : ℝ)*X 1 0+(3859380373/10000000000 : ℝ)*X 1 1+(4572285403/10000000000 : ℝ)*X 1 2+(4204358863/10000000000 : ℝ)*X 2 0+(3859380373/10000000000 : ℝ)*X 2 1+(4572285403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-840364011/5000000000 : ℝ)*X 0 0+(1035691001/2000000000 : ℝ)*X 0 1+(546068427/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277674289/10000000000 : ℝ)*X 1 0+(-308832461/2000000000 : ℝ)*X 1 1+(5460684337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277674559/10000000000 : ℝ)*X 2 0+(2730341931/5000000000 : ℝ)*X 2 1+(-386040649/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((210227617/500000000 : ℝ)*X 0 0+(2283371607/5000000000 : ℝ)*X 0 1+(3864983537/10000000000 : ℝ)*X 0 2+(210227617/500000000 : ℝ)*X 1 0+(2283371607/5000000000 : ℝ)*X 1 1+(3864983537/10000000000 : ℝ)*X 1 2+(210227617/500000000 : ℝ)*X 2 0+(2283371607/5000000000 : ℝ)*X 2 1+(3864983537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1619_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113964056624493386364599169/11921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1443064517/100000000000000 : ℝ)*(base19) + (1395786517/100000000000000 : ℝ)*(base23) + (65771531/100000000000000 : ℝ)*(lower2) + (145301617/50000000000000 : ℝ)*(upper3) + (25016453/20000000000000 : ℝ)*(upper5) + (38207694352971/1562500000000 : ℝ)*(major0) + (38207694352971/1562500000000 : ℝ)*(major1) + (38207694352971/1562500000000 : ℝ)*(major2) + (1743921723562941/50000000000000 : ℝ)*(sp0) + (1743928810095823/50000000000000 : ℝ)*(sp1) + (3487857667469647/100000000000000 : ℝ)*(sp2) + (140271755528353/10000000000000 : ℝ)*(sp3) + (7808065141/50000000000000 : ℝ)*(sp4) + (7939999271/100000000000000 : ℝ)*(sp7) + (701362747641401/50000000000000 : ℝ)*(f.failure) + (871964765814041/25000000000000 : ℝ)*(f.sum) + (295907838189/119218750000000000000000000 : ℝ)*base66 + (25557398651107173/2980468750000000000000000000000 : ℝ)*base67 + (144211044491006817/11921875000000000000000000000000 : ℝ)*base69 + (85733421605479971/5960937500000000000000000000000 : ℝ)*base71 + (760516581079/1907500000000000000000000000 : ℝ)*base74 + (173801412277225567/11921875000000000000000000000000 : ℝ)*base75 + (69453384883667471/5960937500000000000000000000000 : ℝ)*base77 + (168640292841506817/11921875000000000000000000000000 : ℝ)*base79 + (7435282169991/1907500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2903987/2500000000000000000000 : ℝ)*base89 + (2903987/2500000000000000000000 : ℝ)*base91 + (2903987/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214085165094511056377499999/23843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (160332379/12500000000000 : ℝ)*(base19) + (771910857/50000000000000 : ℝ)*(base23) + (43521037/25000000000000 : ℝ)*(upper3) + (55727813/100000000000000 : ℝ)*(lower4) + (153977721/100000000000000 : ℝ)*(upper5) + (621025949101153/25000000000000 : ℝ)*(major0) + (621025949101153/25000000000000 : ℝ)*(major1) + (621025949101153/25000000000000 : ℝ)*(major2) + (15183068919/100000000000000 : ℝ)*(sp1) + (2681004971/20000000000000 : ℝ)*(sp2) + (221451120306577/6250000000000 : ℝ)*(sp4) + (1771600729588641/50000000000000 : ℝ)*(sp5) + (442900372007333/12500000000000 : ℝ)*(sp6) + (1424989368614977/100000000000000 : ℝ)*(sp7) + (1424989368614977/100000000000000 : ℝ)*(f.failure) + (221451120306577/6250000000000 : ℝ)*(f.sum) + (25522554881/14902343750000000000000000 : ℝ)*base65 + (494987683201970139/47687500000000000000000000000000 : ℝ)*base67 + (423731492269907639/47687500000000000000000000000000 : ℝ)*base69 + (200343371031720139/47687500000000000000000000000000 : ℝ)*base71 + (8628559636591/3815000000000000000000000000 : ℝ)*base73 + (585912826095345139/47687500000000000000000000000000 : ℝ)*base75 + (351578869042345139/47687500000000000000000000000000 : ℝ)*base77 + (330002855424532639/47687500000000000000000000000000 : ℝ)*base79 + (671909446737/1907500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (43725301/5000000000000000000000 : ℝ)*base90 + (43725301/5000000000000000000000 : ℝ)*base92 + (43725301/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1619_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (221/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16457/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1619_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1619_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16457/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1619_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1619_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1619_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4791/1024 : ℝ) ≤ p) (hpb : p ≤ (4795/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (87162187/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (83/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16457/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1619_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
