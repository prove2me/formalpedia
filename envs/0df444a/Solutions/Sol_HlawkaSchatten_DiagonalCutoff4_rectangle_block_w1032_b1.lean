-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1032_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:40:14.121638+00:00
-- url     : https://prove2.me/submissions/5c03ad9d-4e22-4ae8-b829-ffa3936db0c5

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
theorem support_rectangle_w1032_s3_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-553850801/2500000000 : ℝ)*x 0 + (2720768523/5000000000 : ℝ)*x 1 + (130515717/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553850801/2500000000 : ℝ)^8225 ≤ (13441136456691/100000000000000 : ℝ)^6177 := by
    have hnat : (553850801 : ℕ)^8225*100000000000000^6177 ≤ 13441136456691^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553850801 2500000000 13441136456691 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720768523/5000000000 : ℝ)^8225 ≤ (8894661183063/20000000000000 : ℝ)^6177 := by
    have hnat : (2720768523 : ℕ)^8225*20000000000000^6177 ≤ 8894661183063^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720768523 5000000000 8894661183063 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130515717/250000000 : ℝ)^8225 ≤ (42085557605921/100000000000000 : ℝ)^6177 := by
    have hnat : (130515717 : ℕ)^8225*100000000000000^6177 ≤ 42085557605921^6177*250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130515717 250000000 42085557605921 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553850801/2500000000 : ℝ), (2720768523/5000000000 : ℝ), (130515717/250000000 : ℝ)] ![(13441136456691/100000000000000 : ℝ), (8894661183063/20000000000000 : ℝ), (42085557605921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553850801/2500000000 : ℝ)|^8225 ≤ (13441136456691/100000000000000 : ℝ)^6177
        have hw : |(-553850801/2500000000 : ℝ)|=(553850801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720768523/5000000000 : ℝ)|^8225 ≤ (8894661183063/20000000000000 : ℝ)^6177
        have hw : |(2720768523/5000000000 : ℝ)|=(2720768523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130515717/250000000 : ℝ)|^8225 ≤ (42085557605921/100000000000000 : ℝ)^6177
        have hw : |(130515717/250000000 : ℝ)|=(130515717/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s3_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356563627/10000000000 : ℝ)*x 0 + (-1164311511/5000000000 : ℝ)*x 1 + (104412583/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356563627/10000000000 : ℝ)^8225 ≤ (21775484540637/50000000000000 : ℝ)^6177 := by
    have hnat : (5356563627 : ℕ)^8225*50000000000000^6177 ≤ 21775484540637^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356563627 10000000000 21775484540637 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164311511/5000000000 : ℝ)^8225 ≤ (1795433531043/12500000000000 : ℝ)^6177 := by
    have hnat : (1164311511 : ℕ)^8225*12500000000000^6177 ≤ 1795433531043^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164311511 5000000000 1795433531043 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104412583/200000000 : ℝ)^8225 ≤ (42085562650983/100000000000000 : ℝ)^6177 := by
    have hnat : (104412583 : ℕ)^8225*100000000000000^6177 ≤ 42085562650983^6177*200000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104412583 200000000 42085562650983 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356563627/10000000000 : ℝ), (-1164311511/5000000000 : ℝ), (104412583/200000000 : ℝ)] ![(21775484540637/50000000000000 : ℝ), (1795433531043/12500000000000 : ℝ), (42085562650983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356563627/10000000000 : ℝ)|^8225 ≤ (21775484540637/50000000000000 : ℝ)^6177
        have hw : |(5356563627/10000000000 : ℝ)|=(5356563627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1164311511/5000000000 : ℝ)|^8225 ≤ (1795433531043/12500000000000 : ℝ)^6177
        have hw : |(-1164311511/5000000000 : ℝ)|=(1164311511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104412583/200000000 : ℝ)|^8225 ≤ (42085562650983/100000000000000 : ℝ)^6177
        have hw : |(104412583/200000000 : ℝ)|=(104412583/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s3_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356563863/10000000000 : ℝ)*x 0 + (2610314517/5000000000 : ℝ)*x 1 + (-145538929/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356563863/10000000000 : ℝ)^8225 ≤ (2177548581811/5000000000000 : ℝ)^6177 := by
    have hnat : (5356563863 : ℕ)^8225*5000000000000^6177 ≤ 2177548581811^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356563863 10000000000 2177548581811 5000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610314517/5000000000 : ℝ)^8225 ≤ (42085561405819/100000000000000 : ℝ)^6177 := by
    have hnat : (2610314517 : ℕ)^8225*100000000000000^6177 ≤ 42085561405819^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610314517 5000000000 42085561405819 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145538929/625000000 : ℝ)^8225 ≤ (179543336883/1250000000000 : ℝ)^6177 := by
    have hnat : (145538929 : ℕ)^8225*1250000000000^6177 ≤ 179543336883^6177*625000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145538929 625000000 179543336883 1250000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356563863/10000000000 : ℝ), (2610314517/5000000000 : ℝ), (-145538929/625000000 : ℝ)] ![(2177548581811/5000000000000 : ℝ), (42085561405819/100000000000000 : ℝ), (179543336883/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356563863/10000000000 : ℝ)|^8225 ≤ (2177548581811/5000000000000 : ℝ)^6177
        have hw : |(5356563863/10000000000 : ℝ)|=(5356563863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610314517/5000000000 : ℝ)|^8225 ≤ (42085561405819/100000000000000 : ℝ)^6177
        have hw : |(2610314517/5000000000 : ℝ)|=(2610314517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145538929/625000000 : ℝ)|^8225 ≤ (179543336883/1250000000000 : ℝ)^6177
        have hw : |(-145538929/625000000 : ℝ)|=(145538929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s3_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094331449/2500000000 : ℝ)*x 0 + (2083848411/5000000000 : ℝ)*x 1 + (22988619/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094331449/2500000000 : ℝ)^8225 ≤ (16642584404053/50000000000000 : ℝ)^6177 := by
    have hnat : (1094331449 : ℕ)^8225*50000000000000^6177 ≤ 16642584404053^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094331449 2500000000 16642584404053 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083848411/5000000000 : ℝ)^8225 ≤ (31179684328757/100000000000000 : ℝ)^6177 := by
    have hnat : (2083848411 : ℕ)^8225*100000000000000^6177 ≤ 31179684328757^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083848411 5000000000 31179684328757 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22988619/50000000 : ℝ)^8225 ≤ (8883786713449/25000000000000 : ℝ)^6177 := by
    have hnat : (22988619 : ℕ)^8225*25000000000000^6177 ≤ 8883786713449^6177*50000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22988619 50000000 8883786713449 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094331449/2500000000 : ℝ), (2083848411/5000000000 : ℝ), (22988619/50000000 : ℝ)] ![(16642584404053/50000000000000 : ℝ), (31179684328757/100000000000000 : ℝ), (8883786713449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094331449/2500000000 : ℝ)|^8225 ≤ (16642584404053/50000000000000 : ℝ)^6177
        have hw : |(1094331449/2500000000 : ℝ)|=(1094331449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083848411/5000000000 : ℝ)|^8225 ≤ (31179684328757/100000000000000 : ℝ)^6177
        have hw : |(2083848411/5000000000 : ℝ)|=(2083848411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22988619/50000000 : ℝ)|^8225 ≤ (8883786713449/25000000000000 : ℝ)^6177
        have hw : |(22988619/50000000 : ℝ)|=(22988619/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s3_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215428411/10000000000 : ℝ)*x 0 + (5221557601/10000000000 : ℝ)*x 1 + (5440602037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215428411/10000000000 : ℝ)^8225 ≤ (6720670048441/50000000000000 : ℝ)^6177 := by
    have hnat : (2215428411 : ℕ)^8225*50000000000000^6177 ≤ 6720670048441^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215428411 10000000000 6720670048441 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221557601/10000000000 : ℝ)^8225 ≤ (5261941137331/12500000000000 : ℝ)^6177 := by
    have hnat : (5221557601 : ℕ)^8225*12500000000000^6177 ≤ 5261941137331^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221557601 10000000000 5261941137331 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440602037/10000000000 : ℝ)^8225 ≤ (44463130795107/100000000000000 : ℝ)^6177 := by
    have hnat : (5440602037 : ℕ)^8225*100000000000000^6177 ≤ 44463130795107^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440602037 10000000000 44463130795107 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215428411/10000000000 : ℝ), (5221557601/10000000000 : ℝ), (5440602037/10000000000 : ℝ)] ![(6720670048441/50000000000000 : ℝ), (5261941137331/12500000000000 : ℝ), (44463130795107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215428411/10000000000 : ℝ)|^8225 ≤ (6720670048441/50000000000000 : ℝ)^6177
        have hw : |(-2215428411/10000000000 : ℝ)|=(2215428411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221557601/10000000000 : ℝ)|^8225 ≤ (5261941137331/12500000000000 : ℝ)^6177
        have hw : |(5221557601/10000000000 : ℝ)|=(5221557601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440602037/10000000000 : ℝ)|^8225 ≤ (44463130795107/100000000000000 : ℝ)^6177
        have hw : |(5440602037/10000000000 : ℝ)|=(5440602037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s3_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301066817/10000000000 : ℝ)*x 0 + (-32947649/156250000 : ℝ)*x 1 + (5440602631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301066817/10000000000 : ℝ)^8225 ≤ (42951192376699/100000000000000 : ℝ)^6177 := by
    have hnat : (5301066817 : ℕ)^8225*100000000000000^6177 ≤ 42951192376699^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301066817 10000000000 42951192376699 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32947649/156250000 : ℝ)^8225 ≤ (6292835175409/50000000000000 : ℝ)^6177 := by
    have hnat : (32947649 : ℕ)^8225*50000000000000^6177 ≤ 6292835175409^6177*156250000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32947649 156250000 6292835175409 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440602631/10000000000 : ℝ)^8225 ≤ (8892627451811/20000000000000 : ℝ)^6177 := by
    have hnat : (5440602631 : ℕ)^8225*20000000000000^6177 ≤ 8892627451811^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440602631 10000000000 8892627451811 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301066817/10000000000 : ℝ), (-32947649/156250000 : ℝ), (5440602631/10000000000 : ℝ)] ![(42951192376699/100000000000000 : ℝ), (6292835175409/50000000000000 : ℝ), (8892627451811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301066817/10000000000 : ℝ)|^8225 ≤ (42951192376699/100000000000000 : ℝ)^6177
        have hw : |(5301066817/10000000000 : ℝ)|=(5301066817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32947649/156250000 : ℝ)|^8225 ≤ (6292835175409/50000000000000 : ℝ)^6177
        have hw : |(-32947649/156250000 : ℝ)|=(32947649/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440602631/10000000000 : ℝ)|^8225 ≤ (8892627451811/20000000000000 : ℝ)^6177
        have hw : |(5440602631/10000000000 : ℝ)|=(5440602631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s3_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325266693/2500000000 : ℝ)*x 0 + (2720301147/5000000000 : ℝ)*x 1 + (-2108650059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325266693/2500000000 : ℝ)^8225 ≤ (21475595945603/50000000000000 : ℝ)^6177 := by
    have hnat : (1325266693 : ℕ)^8225*50000000000000^6177 ≤ 21475595945603^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325266693 2500000000 21475595945603 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720301147/5000000000 : ℝ)^8225 ≤ (22231566795899/50000000000000 : ℝ)^6177 := by
    have hnat : (2720301147 : ℕ)^8225*50000000000000^6177 ≤ 22231566795899^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720301147 5000000000 22231566795899 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108650059/10000000000 : ℝ)^8225 ≤ (6292837253679/50000000000000 : ℝ)^6177 := by
    have hnat : (2108650059 : ℕ)^8225*50000000000000^6177 ≤ 6292837253679^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108650059 10000000000 6292837253679 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325266693/2500000000 : ℝ), (2720301147/5000000000 : ℝ), (-2108650059/10000000000 : ℝ)] ![(21475595945603/50000000000000 : ℝ), (22231566795899/50000000000000 : ℝ), (6292837253679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325266693/2500000000 : ℝ)|^8225 ≤ (21475595945603/50000000000000 : ℝ)^6177
        have hw : |(1325266693/2500000000 : ℝ)|=(1325266693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720301147/5000000000 : ℝ)|^8225 ≤ (22231566795899/50000000000000 : ℝ)^6177
        have hw : |(2720301147/5000000000 : ℝ)|=(2720301147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108650059/10000000000 : ℝ)|^8225 ≤ (6292837253679/50000000000000 : ℝ)^6177
        have hw : |(-2108650059/10000000000 : ℝ)|=(2108650059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s3_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377373581/10000000000 : ℝ)*x 0 + (4595917291/10000000000 : ℝ)*x 1 + (1042378573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377373581/10000000000 : ℝ)^8225 ≤ (33285652637861/100000000000000 : ℝ)^6177 := by
    have hnat : (4377373581 : ℕ)^8225*100000000000000^6177 ≤ 33285652637861^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377373581 10000000000 33285652637861 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4595917291/10000000000 : ℝ)^8225 ≤ (35516556597397/100000000000000 : ℝ)^6177 := by
    have hnat : (4595917291 : ℕ)^8225*100000000000000^6177 ≤ 35516556597397^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595917291 10000000000 35516556597397 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042378573/2500000000 : ℝ)^8225 ≤ (3119779074681/10000000000000 : ℝ)^6177 := by
    have hnat : (1042378573 : ℕ)^8225*10000000000000^6177 ≤ 3119779074681^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042378573 2500000000 3119779074681 10000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377373581/10000000000 : ℝ), (4595917291/10000000000 : ℝ), (1042378573/2500000000 : ℝ)] ![(33285652637861/100000000000000 : ℝ), (35516556597397/100000000000000 : ℝ), (3119779074681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377373581/10000000000 : ℝ)|^8225 ≤ (33285652637861/100000000000000 : ℝ)^6177
        have hw : |(4377373581/10000000000 : ℝ)|=(4377373581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4595917291/10000000000 : ℝ)|^8225 ≤ (35516556597397/100000000000000 : ℝ)^6177
        have hw : |(4595917291/10000000000 : ℝ)|=(4595917291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042378573/2500000000 : ℝ)|^8225 ≤ (3119779074681/10000000000000 : ℝ)^6177
        have hw : |(1042378573/2500000000 : ℝ)|=(1042378573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16851/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4273/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5141/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2991/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16851/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4273/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16851/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4273/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16851/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4273/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16851/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4273/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16851/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4273/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16851/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4273/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4273/50000 : ℝ) ^ (257/64 : ℝ) ≤ (5132870992982873/100000000000000000000 : ℝ) := by
    have hpowers : (4273/50000 : ℝ)^257 ≤ (5132870992982873/100000000000000000000 : ℝ)^64 := by
      have hnat : (4273 : ℕ)^257*100000000000000000000^64 ≤ 5132870992982873^64*50000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4273 50000 5132870992982873 100000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4273/50000 : ℝ)) (X := (5132870992982873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (16851/100000 : ℝ) ^ (257/64 : ℝ) ≤ (3136741515398239/4000000000000000000 : ℝ) := by
    have hpowers : (16851/100000 : ℝ)^257 ≤ (3136741515398239/4000000000000000000 : ℝ)^64 := by
      have hnat : (16851 : ℕ)^257*4000000000000000000^64 ≤ 3136741515398239^64*100000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16851 100000 3136741515398239 4000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16851/100000 : ℝ)) (X := (3136741515398239/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005132870992982873/50000000000000000000 : ℝ) ≤ (5000127817541499/5000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (50005132870992982873/50000000000000000000 : ℝ)^64 ≤ (5000127817541499/5000000000000000 : ℝ)^257 := by
      have hnat : (50005132870992982873 : ℕ)^64*5000000000000000^257 ≤ 5000127817541499^257*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005132870992982873 50000000000000000000 5000127817541499 5000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000127817541499/5000000000000000 : ℝ)) (X := (50005132870992982873/50000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (3127610981527435589/3125000000000000000 : ℝ) ≤ (10002080005218549/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (3127610981527435589/3125000000000000000 : ℝ)^64 ≤ (10002080005218549/10000000000000000 : ℝ)^257 := by
      have hnat : (3127610981527435589 : ℕ)^64*10000000000000000^257 ≤ 10002080005218549^257*3125000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127610981527435589 3125000000000000000 10002080005218549 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002080005218549/10000000000000000 : ℝ)) (X := (3127610981527435589/3125000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (2003136741515398239/2000000000000000000 : ℝ) ≤ (100039043753541/100000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (2003136741515398239/2000000000000000000 : ℝ)^64 ≤ (100039043753541/100000000000000 : ℝ)^257 := by
      have hnat : (2003136741515398239 : ℕ)^64*100000000000000^257 ≤ 100039043753541^257*2000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2003136741515398239 2000000000000000000 100039043753541 100000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100039043753541/100000000000000 : ℝ)) (X := (2003136741515398239/2000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5132870992982873/100000000000000000000 : ℝ) ≤ ((41510470457503730349/41525000000000000000 : ℝ)+2*(1824370135551/830500000000000 : ℝ)*(4273/50000 : ℝ))^(257/64 : ℝ) := by
    rw [show (41510470457503730349/41525000000000000000 : ℝ)+2*(1824370135551/830500000000000 : ℝ)*(4273/50000 : ℝ)=(5000127817541499/5000000000000000 : ℝ) by norm_num, show 1+2*(5132870992982873/100000000000000000000 : ℝ)=(50005132870992982873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3136741515398239/4000000000000000000 : ℝ)+(5132870992982873/100000000000000000000 : ℝ) ≤ ((41510470457503730349/41525000000000000000 : ℝ)+(1824370135551/830500000000000 : ℝ)*((16851/100000 : ℝ)+(4273/50000 : ℝ)))^(257/64 : ℝ) := by
    rw [show (41510470457503730349/41525000000000000000 : ℝ)+(1824370135551/830500000000000 : ℝ)*((16851/100000 : ℝ)+(4273/50000 : ℝ))=(10002080005218549/10000000000000000 : ℝ) by norm_num, show 1+(3136741515398239/4000000000000000000 : ℝ)+(5132870992982873/100000000000000000000 : ℝ)=(3127610981527435589/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3136741515398239/4000000000000000000 : ℝ) ≤ ((41510470457503730349/41525000000000000000 : ℝ)+2*(1824370135551/830500000000000 : ℝ)*(16851/100000 : ℝ))^(257/64 : ℝ) := by
    rw [show (41510470457503730349/41525000000000000000 : ℝ)+2*(1824370135551/830500000000000 : ℝ)*(16851/100000 : ℝ)=(100039043753541/100000000000000 : ℝ) by norm_num, show 1+2*(3136741515398239/4000000000000000000 : ℝ)=(2003136741515398239/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41510470457503730349/41525000000000000000 : ℝ)*(X 1 0+X 2 0)+(1824370135551/830500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (4273/50000 : ℝ)) (hi := (16851/100000 : ℝ)) (c := (41510470457503730349/41525000000000000000 : ℝ)) (alpha := (1824370135551/830500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41510470457503730349/41525000000000000000 : ℝ)*(X 0 1+X 2 1)+(1824370135551/830500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (4273/50000 : ℝ)) (hi := (16851/100000 : ℝ)) (c := (41510470457503730349/41525000000000000000 : ℝ)) (alpha := (1824370135551/830500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41510470457503730349/41525000000000000000 : ℝ)*(X 0 2+X 1 2)+(1824370135551/830500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (4273/50000 : ℝ)) (hi := (16851/100000 : ℝ)) (c := (41510470457503730349/41525000000000000000 : ℝ)) (alpha := (1824370135551/830500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-553850801/2500000000 : ℝ)*X 0 0+(2720768523/5000000000 : ℝ)*X 0 1+(130515717/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356563627/10000000000 : ℝ)*X 1 0+(-1164311511/5000000000 : ℝ)*X 1 1+(104412583/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356563863/10000000000 : ℝ)*X 2 0+(2610314517/5000000000 : ℝ)*X 2 1+(-145538929/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094331449/2500000000 : ℝ)*X 0 0+(2083848411/5000000000 : ℝ)*X 0 1+(22988619/50000000 : ℝ)*X 0 2+(1094331449/2500000000 : ℝ)*X 1 0+(2083848411/5000000000 : ℝ)*X 1 1+(22988619/50000000 : ℝ)*X 1 2+(1094331449/2500000000 : ℝ)*X 2 0+(2083848411/5000000000 : ℝ)*X 2 1+(22988619/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2215428411/10000000000 : ℝ)*X 0 0+(5221557601/10000000000 : ℝ)*X 0 1+(5440602037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301066817/10000000000 : ℝ)*X 1 0+(-32947649/156250000 : ℝ)*X 1 1+(5440602631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325266693/2500000000 : ℝ)*X 2 0+(2720301147/5000000000 : ℝ)*X 2 1+(-2108650059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377373581/10000000000 : ℝ)*X 0 0+(4595917291/10000000000 : ℝ)*X 0 1+(1042378573/2500000000 : ℝ)*X 0 2+(4377373581/10000000000 : ℝ)*X 1 0+(4595917291/10000000000 : ℝ)*X 1 1+(1042378573/2500000000 : ℝ)*X 1 2+(4377373581/10000000000 : ℝ)*X 2 0+(4595917291/10000000000 : ℝ)*X 2 1+(1042378573/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107923801140354433076241339/25953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62243193/6250000000000 : ℝ)*(base19) + (852025553/100000000000000 : ℝ)*(base23) + (55652809/25000000000000 : ℝ)*(lower2) + (967893/2500000000000 : ℝ)*(lower4) + (2953667/4000000000000 : ℝ)*(lower5) + (2676670998607/78125000000 : ℝ)*(major0) + (2676670998607/78125000000 : ℝ)*(major1) + (2676670998607/78125000000 : ℝ)*(major2) + (4526792724428827/100000000000000 : ℝ)*(sp0) + (2263411519210541/50000000000000 : ℝ)*(sp1) + (4526823182286617/100000000000000 : ℝ)*(sp2) + (465088639324189/20000000000000 : ℝ)*(sp3) + (1956867709/6250000000000 : ℝ)*(sp4) + (5193443521/50000000000000 : ℝ)*(sp7) + (581363395876997/25000000000000 : ℝ)*(f.failure) + (452682403431217/10000000000000 : ℝ)*(f.sum) + (10110121148671/4152500000000000000000000000 : ℝ)*base65 + (234373356542776503/12976562500000000000000000000000 : ℝ)*base68 + (21420905956708391/1622070312500000000000000000000 : ℝ)*base70 + (25870064487474189/6488281250000000000000000000000 : ℝ)*base72 + (497175788257/129765625000000000000000000 : ℝ)*base74 + (42719395852338311/6488281250000000000000000000000 : ℝ)*base75 + (180808555632349881/25953125000000000000000000000000 : ℝ)*base78 + (94939161161035997/12976562500000000000000000000000 : ℝ)*base79 + (225226115457/519062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (37516793/2500000000000000000000 : ℝ)*base89 + (37516793/2500000000000000000000 : ℝ)*base91 + (37516793/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1214309389926510428689959741/519062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (430874571/50000000000000 : ℝ)*(base19) + (847080789/100000000000000 : ℝ)*(base23) + (51256981/100000000000000 : ℝ)*(upper2) + (63685467/50000000000000 : ℝ)*(upper3) + (863810757555303/25000000000000 : ℝ)*(major0) + (863810757555303/25000000000000 : ℝ)*(major1) + (863810757555303/25000000000000 : ℝ)*(major2) + (12199476757/50000000000000 : ℝ)*(sp1) + (8527103/48828125000 : ℝ)*(sp2) + (469506471/12500000000000 : ℝ)*(sp3) + (4565278280110399/100000000000000 : ℝ)*(sp4) + (2282626509703871/50000000000000 : ℝ)*(sp5) + (2282629984761333/50000000000000 : ℝ)*(sp6) + (469040789259863/20000000000000 : ℝ)*(sp7) + (2345207702351083/100000000000000 : ℝ)*(f.failure) + (4565278280110399/100000000000000 : ℝ)*(f.sum) + (23910433821019/20762500000000000000000000000 : ℝ)*base66 + (10533754755085359253/1038125000000000000000000000000000 : ℝ)*base68 + (10606570278312234253/1038125000000000000000000000000000 : ℝ)*base70 + (2187652349819734253/1038125000000000000000000000000000 : ℝ)*base72 + (16414330292213/41525000000000000000000000000 : ℝ)*base74 + (3422630687763390747/1038125000000000000000000000000000 : ℝ)*base75 + (1084428026772765747/1038125000000000000000000000000000 : ℝ)*base77 + (13662679181810984253/1038125000000000000000000000000000 : ℝ)*base80 + (100067805291969/20762500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (22780727/10000000000000000000000 : ℝ)*base89 + (22780727/10000000000000000000000 : ℝ)*base91 + (22780727/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1032_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16851/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4273/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5141/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1032_s4_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-554855507/2500000000 : ℝ)*x 0 + (5407733761/10000000000 : ℝ)*x 1 + (1312951987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554855507/2500000000 : ℝ)^8225 ≤ (6736806546193/50000000000000 : ℝ)^6177 := by
    have hnat : (554855507 : ℕ)^8225*50000000000000^6177 ≤ 6736806546193^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554855507 2500000000 6736806546193 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407733761/10000000000 : ℝ)^8225 ≤ (44105814717931/100000000000000 : ℝ)^6177 := by
    have hnat : (5407733761 : ℕ)^8225*100000000000000^6177 ≤ 44105814717931^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407733761 10000000000 44105814717931 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1312951987/2500000000 : ℝ)^8225 ≤ (42420572179347/100000000000000 : ℝ)^6177 := by
    have hnat : (1312951987 : ℕ)^8225*100000000000000^6177 ≤ 42420572179347^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312951987 2500000000 42420572179347 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554855507/2500000000 : ℝ), (5407733761/10000000000 : ℝ), (1312951987/2500000000 : ℝ)] ![(6736806546193/50000000000000 : ℝ), (44105814717931/100000000000000 : ℝ), (42420572179347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554855507/2500000000 : ℝ)|^8225 ≤ (6736806546193/50000000000000 : ℝ)^6177
        have hw : |(-554855507/2500000000 : ℝ)|=(554855507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407733761/10000000000 : ℝ)|^8225 ≤ (44105814717931/100000000000000 : ℝ)^6177
        have hw : |(5407733761/10000000000 : ℝ)|=(5407733761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1312951987/2500000000 : ℝ)|^8225 ≤ (42420572179347/100000000000000 : ℝ)^6177
        have hw : |(1312951987/2500000000 : ℝ)|=(1312951987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s4_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668527673/1250000000 : ℝ)*x 0 + (-2298763841/10000000000 : ℝ)*x 1 + (5251808011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668527673/1250000000 : ℝ)^8225 ≤ (43460678901421/100000000000000 : ℝ)^6177 := by
    have hnat : (668527673 : ℕ)^8225*100000000000000^6177 ≤ 43460678901421^6177*1250000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668527673 1250000000 43460678901421 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2298763841/10000000000 : ℝ)^8225 ≤ (352968705551/2500000000000 : ℝ)^6177 := by
    have hnat : (2298763841 : ℕ)^8225*2500000000000^6177 ≤ 352968705551^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298763841 10000000000 352968705551 2500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5251808011/10000000000 : ℝ)^8225 ≤ (42420572856937/100000000000000 : ℝ)^6177 := by
    have hnat : (5251808011 : ℕ)^8225*100000000000000^6177 ≤ 42420572856937^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251808011 10000000000 42420572856937 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668527673/1250000000 : ℝ), (-2298763841/10000000000 : ℝ), (5251808011/10000000000 : ℝ)] ![(43460678901421/100000000000000 : ℝ), (352968705551/2500000000000 : ℝ), (42420572856937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668527673/1250000000 : ℝ)|^8225 ≤ (43460678901421/100000000000000 : ℝ)^6177
        have hw : |(668527673/1250000000 : ℝ)|=(668527673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2298763841/10000000000 : ℝ)|^8225 ≤ (352968705551/2500000000000 : ℝ)^6177
        have hw : |(-2298763841/10000000000 : ℝ)|=(2298763841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5251808011/10000000000 : ℝ)|^8225 ≤ (42420572856937/100000000000000 : ℝ)^6177
        have hw : |(5251808011/10000000000 : ℝ)|=(5251808011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s4_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5348221499/10000000000 : ℝ)*x 0 + (5251807881/10000000000 : ℝ)*x 1 + (-114938193/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348221499/10000000000 : ℝ)^8225 ≤ (43460680145773/100000000000000 : ℝ)^6177 := by
    have hnat : (5348221499 : ℕ)^8225*100000000000000^6177 ≤ 43460680145773^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348221499 10000000000 43460680145773 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5251807881/10000000000 : ℝ)^8225 ≤ (2651285716171/6250000000000 : ℝ)^6177 := by
    have hnat : (5251807881 : ℕ)^8225*6250000000000^6177 ≤ 2651285716171^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251807881 10000000000 2651285716171 6250000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114938193/500000000 : ℝ)^8225 ≤ (7059374188713/50000000000000 : ℝ)^6177 := by
    have hnat : (114938193 : ℕ)^8225*50000000000000^6177 ≤ 7059374188713^6177*500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114938193 500000000 7059374188713 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348221499/10000000000 : ℝ), (5251807881/10000000000 : ℝ), (-114938193/500000000 : ℝ)] ![(43460680145773/100000000000000 : ℝ), (2651285716171/6250000000000 : ℝ), (7059374188713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348221499/10000000000 : ℝ)|^8225 ≤ (43460680145773/100000000000000 : ℝ)^6177
        have hw : |(5348221499/10000000000 : ℝ)|=(5348221499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5251807881/10000000000 : ℝ)|^8225 ≤ (2651285716171/6250000000000 : ℝ)^6177
        have hw : |(5251807881/10000000000 : ℝ)|=(5251807881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114938193/500000000 : ℝ)|^8225 ≤ (7059374188713/50000000000000 : ℝ)^6177
        have hw : |(-114938193/500000000 : ℝ)|=(114938193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s4_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875942259/2000000000 : ℝ)*x 0 + (423062983/1000000000 : ℝ)*x 1 + (4534161473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875942259/2000000000 : ℝ)^8225 ≤ (6661864890919/20000000000000 : ℝ)^6177 := by
    have hnat : (875942259 : ℕ)^8225*20000000000000^6177 ≤ 6661864890919^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875942259 2000000000 6661864890919 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423062983/1000000000 : ℝ)^8225 ≤ (7952042201347/25000000000000 : ℝ)^6177 := by
    have hnat : (423062983 : ℕ)^8225*25000000000000^6177 ≤ 7952042201347^6177*1000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423062983 1000000000 7952042201347 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4534161473/10000000000 : ℝ)^8225 ≤ (1090078335107/3125000000000 : ℝ)^6177 := by
    have hnat : (4534161473 : ℕ)^8225*3125000000000^6177 ≤ 1090078335107^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534161473 10000000000 1090078335107 3125000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875942259/2000000000 : ℝ), (423062983/1000000000 : ℝ), (4534161473/10000000000 : ℝ)] ![(6661864890919/20000000000000 : ℝ), (7952042201347/25000000000000 : ℝ), (1090078335107/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875942259/2000000000 : ℝ)|^8225 ≤ (6661864890919/20000000000000 : ℝ)^6177
        have hw : |(875942259/2000000000 : ℝ)|=(875942259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423062983/1000000000 : ℝ)|^8225 ≤ (7952042201347/25000000000000 : ℝ)^6177
        have hw : |(423062983/1000000000 : ℝ)|=(423062983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4534161473/10000000000 : ℝ)|^8225 ≤ (1090078335107/3125000000000 : ℝ)^6177
        have hw : |(4534161473/10000000000 : ℝ)|=(4534161473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s4_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2219430351/10000000000 : ℝ)*x 0 + (2626135861/5000000000 : ℝ)*x 1 + (168977133/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219430351/10000000000 : ℝ)^8225 ≤ (1347368037187/10000000000000 : ℝ)^6177 := by
    have hnat : (2219430351 : ℕ)^8225*10000000000000^6177 ≤ 1347368037187^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219430351 10000000000 1347368037187 10000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626135861/5000000000 : ℝ)^8225 ≤ (21212780160319/50000000000000 : ℝ)^6177 := by
    have hnat : (2626135861 : ℕ)^8225*50000000000000^6177 ≤ 21212780160319^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626135861 5000000000 21212780160319 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168977133/312500000 : ℝ)^8225 ≤ (44100759300697/100000000000000 : ℝ)^6177 := by
    have hnat : (168977133 : ℕ)^8225*100000000000000^6177 ≤ 44100759300697^6177*312500000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168977133 312500000 44100759300697 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2219430351/10000000000 : ℝ), (2626135861/5000000000 : ℝ), (168977133/312500000 : ℝ)] ![(1347368037187/10000000000000 : ℝ), (21212780160319/50000000000000 : ℝ), (44100759300697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2219430351/10000000000 : ℝ)|^8225 ≤ (1347368037187/10000000000000 : ℝ)^6177
        have hw : |(-2219430351/10000000000 : ℝ)|=(2219430351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626135861/5000000000 : ℝ)|^8225 ≤ (21212780160319/50000000000000 : ℝ)^6177
        have hw : |(2626135861/5000000000 : ℝ)|=(2626135861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168977133/312500000 : ℝ)|^8225 ≤ (44100759300697/100000000000000 : ℝ)^6177
        have hw : |(168977133/312500000 : ℝ)|=(168977133/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s4_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20738501/39062500 : ℝ)*x 0 + (-1071651743/5000000000 : ℝ)*x 1 + (2703634167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20738501/39062500 : ℝ)^8225 ≤ (21518704895557/50000000000000 : ℝ)^6177 := by
    have hnat : (20738501 : ℕ)^8225*50000000000000^6177 ≤ 21518704895557^6177*39062500^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20738501 39062500 21518704895557 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071651743/5000000000 : ℝ)^8225 ≤ (12861830042067/100000000000000 : ℝ)^6177 := by
    have hnat : (1071651743 : ℕ)^8225*100000000000000^6177 ≤ 12861830042067^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071651743 5000000000 12861830042067 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703634167/5000000000 : ℝ)^8225 ≤ (4410076014777/10000000000000 : ℝ)^6177 := by
    have hnat : (2703634167 : ℕ)^8225*10000000000000^6177 ≤ 4410076014777^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703634167 5000000000 4410076014777 10000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20738501/39062500 : ℝ), (-1071651743/5000000000 : ℝ), (2703634167/5000000000 : ℝ)] ![(21518704895557/50000000000000 : ℝ), (12861830042067/100000000000000 : ℝ), (4410076014777/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20738501/39062500 : ℝ)|^8225 ≤ (21518704895557/50000000000000 : ℝ)^6177
        have hw : |(20738501/39062500 : ℝ)|=(20738501/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071651743/5000000000 : ℝ)|^8225 ≤ (12861830042067/100000000000000 : ℝ)^6177
        have hw : |(-1071651743/5000000000 : ℝ)|=(1071651743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703634167/5000000000 : ℝ)|^8225 ≤ (4410076014777/10000000000000 : ℝ)^6177
        have hw : |(2703634167/5000000000 : ℝ)|=(2703634167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s4_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327264003/2500000000 : ℝ)*x 0 + (5407268627/10000000000 : ℝ)*x 1 + (-2143303417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327264003/2500000000 : ℝ)^8225 ≤ (43037407157349/100000000000000 : ℝ)^6177 := by
    have hnat : (1327264003 : ℕ)^8225*100000000000000^6177 ≤ 43037407157349^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327264003 2500000000 43037407157349 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407268627/10000000000 : ℝ)^8225 ≤ (22050381664863/50000000000000 : ℝ)^6177 := by
    have hnat : (5407268627 : ℕ)^8225*50000000000000^6177 ≤ 22050381664863^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407268627 10000000000 22050381664863 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2143303417/10000000000 : ℝ)^8225 ≤ (6430914745359/50000000000000 : ℝ)^6177 := by
    have hnat : (2143303417 : ℕ)^8225*50000000000000^6177 ≤ 6430914745359^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143303417 10000000000 6430914745359 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327264003/2500000000 : ℝ), (5407268627/10000000000 : ℝ), (-2143303417/10000000000 : ℝ)] ![(43037407157349/100000000000000 : ℝ), (22050381664863/50000000000000 : ℝ), (6430914745359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327264003/2500000000 : ℝ)|^8225 ≤ (43037407157349/100000000000000 : ℝ)^6177
        have hw : |(1327264003/2500000000 : ℝ)|=(1327264003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407268627/10000000000 : ℝ)|^8225 ≤ (22050381664863/50000000000000 : ℝ)^6177
        have hw : |(5407268627/10000000000 : ℝ)|=(5407268627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2143303417/10000000000 : ℝ)|^8225 ≤ (6430914745359/50000000000000 : ℝ)^6177
        have hw : |(-2143303417/10000000000 : ℝ)|=(2143303417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s4_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379728281/10000000000 : ℝ)*x 0 + (2266629727/5000000000 : ℝ)*x 1 + (2115767783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379728281/10000000000 : ℝ)^8225 ≤ (33309496471071/100000000000000 : ℝ)^6177 := by
    have hnat : (4379728281 : ℕ)^8225*100000000000000^6177 ≤ 33309496471071^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379728281 10000000000 33309496471071 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266629727/5000000000 : ℝ)^8225 ≤ (1743663337873/5000000000000 : ℝ)^6177 := by
    have hnat : (2266629727 : ℕ)^8225*5000000000000^6177 ≤ 1743663337873^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266629727 5000000000 1743663337873 5000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115767783/5000000000 : ℝ)^8225 ≤ (15908618376349/50000000000000 : ℝ)^6177 := by
    have hnat : (2115767783 : ℕ)^8225*50000000000000^6177 ≤ 15908618376349^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115767783 5000000000 15908618376349 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379728281/10000000000 : ℝ), (2266629727/5000000000 : ℝ), (2115767783/5000000000 : ℝ)] ![(33309496471071/100000000000000 : ℝ), (1743663337873/5000000000000 : ℝ), (15908618376349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379728281/10000000000 : ℝ)|^8225 ≤ (33309496471071/100000000000000 : ℝ)^6177
        have hw : |(4379728281/10000000000 : ℝ)|=(4379728281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266629727/5000000000 : ℝ)|^8225 ≤ (1743663337873/5000000000000 : ℝ)^6177
        have hw : |(2266629727/5000000000 : ℝ)|=(2266629727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115767783/5000000000 : ℝ)|^8225 ≤ (15908618376349/50000000000000 : ℝ)^6177
        have hw : |(2115767783/5000000000 : ℝ)|=(2115767783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5141/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2737/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14249/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2991/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5141/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2991/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5141/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2991/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5141/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2991/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5141/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2991/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5141/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2991/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5141/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5141/50000 : ℝ) ^ (257/64 : ℝ) ≤ (2696585030427121/25000000000000000000 : ℝ) := by
    have hpowers : (5141/50000 : ℝ)^257 ≤ (2696585030427121/25000000000000000000 : ℝ)^64 := by
      have hnat : (5141 : ℕ)^257*25000000000000000000^64 ≤ 2696585030427121^64*50000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5141 50000 2696585030427121 25000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5141/50000 : ℝ)) (X := (2696585030427121/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2991/20000 : ℝ) ^ (257/64 : ℝ) ≤ (24278492195132913/50000000000000000000 : ℝ) := by
    have hpowers : (2991/20000 : ℝ)^257 ≤ (24278492195132913/50000000000000000000 : ℝ)^64 := by
      have hnat : (2991 : ℕ)^257*50000000000000000000^64 ≤ 24278492195132913^64*20000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2991 20000 24278492195132913 50000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2991/20000 : ℝ)) (X := (24278492195132913/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502696585030427121/12500000000000000000 : ℝ) ≤ (1250067146873223/1250000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (12502696585030427121/12500000000000000000 : ℝ)^64 ≤ (1250067146873223/1250000000000000 : ℝ)^257 := by
      have hnat : (12502696585030427121 : ℕ)^64*1250000000000000^257 ≤ 1250067146873223^257*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502696585030427121 12500000000000000000 1250067146873223 1250000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250067146873223/1250000000000000 : ℝ)) (X := (12502696585030427121/12500000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005934332451197431/10000000000000000000 : ℝ) ≤ (10001477481235137/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (10005934332451197431/10000000000000000000 : ℝ)^64 ≤ (10001477481235137/10000000000000000 : ℝ)^257 := by
      have hnat : (10005934332451197431 : ℕ)^64*10000000000000000^257 ≤ 10001477481235137^257*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005934332451197431 10000000000000000000 10001477481235137 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001477481235137/10000000000000000 : ℝ)) (X := (10005934332451197431/10000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25024278492195132913/25000000000000000000 : ℝ) ≤ (1000241778748449/1000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (25024278492195132913/25000000000000000000 : ℝ)^64 ≤ (1000241778748449/1000000000000000 : ℝ)^257 := by
      have hnat : (25024278492195132913 : ℕ)^64*1000000000000000^257 ≤ 1000241778748449^257*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024278492195132913 25000000000000000000 1000241778748449 1000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000241778748449/1000000000000000 : ℝ)) (X := (25024278492195132913/25000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2696585030427121/25000000000000000000 : ℝ) ≤ ((2335658688049843677/2336500000000000000 : ℝ)+2*(940306249353/467300000000000 : ℝ)*(5141/50000 : ℝ))^(257/64 : ℝ) := by
    rw [show (2335658688049843677/2336500000000000000 : ℝ)+2*(940306249353/467300000000000 : ℝ)*(5141/50000 : ℝ)=(1250067146873223/1250000000000000 : ℝ) by norm_num, show 1+2*(2696585030427121/25000000000000000000 : ℝ)=(12502696585030427121/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24278492195132913/50000000000000000000 : ℝ)+(2696585030427121/25000000000000000000 : ℝ) ≤ ((2335658688049843677/2336500000000000000 : ℝ)+(940306249353/467300000000000 : ℝ)*((2991/20000 : ℝ)+(5141/50000 : ℝ)))^(257/64 : ℝ) := by
    rw [show (2335658688049843677/2336500000000000000 : ℝ)+(940306249353/467300000000000 : ℝ)*((2991/20000 : ℝ)+(5141/50000 : ℝ))=(10001477481235137/10000000000000000 : ℝ) by norm_num, show 1+(24278492195132913/50000000000000000000 : ℝ)+(2696585030427121/25000000000000000000 : ℝ)=(10005934332451197431/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24278492195132913/50000000000000000000 : ℝ) ≤ ((2335658688049843677/2336500000000000000 : ℝ)+2*(940306249353/467300000000000 : ℝ)*(2991/20000 : ℝ))^(257/64 : ℝ) := by
    rw [show (2335658688049843677/2336500000000000000 : ℝ)+2*(940306249353/467300000000000 : ℝ)*(2991/20000 : ℝ)=(1000241778748449/1000000000000000 : ℝ) by norm_num, show 1+2*(24278492195132913/50000000000000000000 : ℝ)=(25024278492195132913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2335658688049843677/2336500000000000000 : ℝ)*(X 1 0+X 2 0)+(940306249353/467300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (5141/50000 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (2335658688049843677/2336500000000000000 : ℝ)) (alpha := (940306249353/467300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2335658688049843677/2336500000000000000 : ℝ)*(X 0 1+X 2 1)+(940306249353/467300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (5141/50000 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (2335658688049843677/2336500000000000000 : ℝ)) (alpha := (940306249353/467300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2335658688049843677/2336500000000000000 : ℝ)*(X 0 2+X 1 2)+(940306249353/467300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (5141/50000 : ℝ)) (hi := (2991/20000 : ℝ)) (c := (2335658688049843677/2336500000000000000 : ℝ)) (alpha := (940306249353/467300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-554855507/2500000000 : ℝ)*X 0 0+(5407733761/10000000000 : ℝ)*X 0 1+(1312951987/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668527673/1250000000 : ℝ)*X 1 0+(-2298763841/10000000000 : ℝ)*X 1 1+(5251808011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348221499/10000000000 : ℝ)*X 2 0+(5251807881/10000000000 : ℝ)*X 2 1+(-114938193/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875942259/2000000000 : ℝ)*X 0 0+(423062983/1000000000 : ℝ)*X 0 1+(4534161473/10000000000 : ℝ)*X 0 2+(875942259/2000000000 : ℝ)*X 1 0+(423062983/1000000000 : ℝ)*X 1 1+(4534161473/10000000000 : ℝ)*X 1 2+(875942259/2000000000 : ℝ)*X 2 0+(423062983/1000000000 : ℝ)*X 2 1+(4534161473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2219430351/10000000000 : ℝ)*X 0 0+(2626135861/5000000000 : ℝ)*X 0 1+(168977133/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20738501/39062500 : ℝ)*X 1 0+(-1071651743/5000000000 : ℝ)*X 1 1+(2703634167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327264003/2500000000 : ℝ)*X 2 0+(5407268627/10000000000 : ℝ)*X 2 1+(-2143303417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379728281/10000000000 : ℝ)*X 0 0+(2266629727/5000000000 : ℝ)*X 0 1+(2115767783/5000000000 : ℝ)*X 0 2+(4379728281/10000000000 : ℝ)*X 1 0+(2266629727/5000000000 : ℝ)*X 1 1+(2115767783/5000000000 : ℝ)*X 1 2+(4379728281/10000000000 : ℝ)*X 2 0+(2266629727/5000000000 : ℝ)*X 2 1+(2115767783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (258556650445546147789128051/58412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (949612021/100000000000000 : ℝ)*(base19) + (1081317427/100000000000000 : ℝ)*(base23) + (54983043/50000000000000 : ℝ)*(upper3) + (103581/3125000000000 : ℝ)*(upper4) + (134149/125000000000 : ℝ)*(upper5) + (4853964131823079/100000000000000 : ℝ)*(major0) + (4853964131823079/100000000000000 : ℝ)*(major1) + (4853964131823079/100000000000000 : ℝ)*(major2) + (400833095239393/6250000000000 : ℝ)*(sp0) + (1282670620688337/20000000000000 : ℝ)*(sp1) + (6413352971736279/100000000000000 : ℝ)*(sp2) + (3294561364746017/100000000000000 : ℝ)*(sp3) + (12264611709/50000000000000 : ℝ)*(sp4) + (3174575003/25000000000000 : ℝ)*(sp7) + (329457406304603/10000000000000 : ℝ)*(f.failure) + (3206677026526853/50000000000000 : ℝ)*(f.sum) + (11216942638531/11682500000000000000000000000 : ℝ)*base65 + (1875867358744956483/233650000000000000000000000000000 : ℝ)*base67 + (274234379903006483/233650000000000000000000000000000 : ℝ)*base69 + (1522482503841706483/233650000000000000000000000000000 : ℝ)*base71 + (72657186023121/11682500000000000000000000000 : ℝ)*base73 + (1723377441122943517/233650000000000000000000000000000 : ℝ)*base76 + (823385306051056483/233650000000000000000000000000000 : ℝ)*base77 + (270160109897206483/233650000000000000000000000000000 : ℝ)*base79 + (29221976063529/11682500000000000000000000000 : ℝ)*base82 + (14213607/1000000000000000000000 : ℝ)*base89 + (14213607/1000000000000000000000 : ℝ)*base91 + (14213607/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140657356339116965846334333/29206250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138256661/100000000000000 : ℝ)*(base19) + (220429819/50000000000000 : ℝ)*(base23) + (66462167/100000000000000 : ℝ)*(upper3) + (51843517/20000000000000 : ℝ)*(lower4) + (1220755447624957/25000000000000 : ℝ)*(major0) + (1220755447624957/25000000000000 : ℝ)*(major1) + (1220755447624957/25000000000000 : ℝ)*(major2) + (23799799/781250000000 : ℝ)*(sp1) + (18074539199/100000000000000 : ℝ)*(sp2) + (314084491/6250000000000 : ℝ)*(sp3) + (6451746795405049/100000000000000 : ℝ)*(sp4) + (1612935902693529/25000000000000 : ℝ)*(sp5) + (1612932070001553/25000000000000 : ℝ)*(sp6) + (3314291599709337/100000000000000 : ℝ)*(sp7) + (414287078132649/12500000000000 : ℝ)*(f.failure) + (6451746795405049/100000000000000 : ℝ)*(f.sum) + (37637605062143/11682500000000000000000000000 : ℝ)*base66 + (1318077017661851889/58412500000000000000000000000000 : ℝ)*base67 + (381033195324176889/58412500000000000000000000000000 : ℝ)*base69 + (606297356486460611/58412500000000000000000000000000 : ℝ)*base72 + (25245923999267/11682500000000000000000000000 : ℝ)*base73 + (571007515321476889/58412500000000000000000000000000 : ℝ)*base75 + (787112298171123111/58412500000000000000000000000000 : ℝ)*base78 + (1676401847772539389/58412500000000000000000000000000 : ℝ)*base79 + (15730792141553/11682500000000000000000000000 : ℝ)*base82 + (16379219/1250000000000000000000 : ℝ)*base90 + (16379219/1250000000000000000000 : ℝ)*base92 + (16379219/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1032_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2991/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5141/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2737/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1032_s5_0 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110176079/5000000000 : ℝ)*x 0 + (5397987993/10000000000 : ℝ)*x 1 + (5260944021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110176079/5000000000 : ℝ)^8225 ≤ (13481132373229/100000000000000 : ℝ)^6177 := by
    have hnat : (1110176079 : ℕ)^8225*100000000000000^6177 ≤ 13481132373229^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110176079 5000000000 13481132373229 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397987993/10000000000 : ℝ)^8225 ≤ (44000005111421/100000000000000 : ℝ)^6177 := by
    have hnat : (5397987993 : ℕ)^8225*100000000000000^6177 ≤ 44000005111421^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397987993 10000000000 44000005111421 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260944021/10000000000 : ℝ)^8225 ≤ (42518862495031/100000000000000 : ℝ)^6177 := by
    have hnat : (5260944021 : ℕ)^8225*100000000000000^6177 ≤ 42518862495031^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260944021 10000000000 42518862495031 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110176079/5000000000 : ℝ), (5397987993/10000000000 : ℝ), (5260944021/10000000000 : ℝ)] ![(13481132373229/100000000000000 : ℝ), (44000005111421/100000000000000 : ℝ), (42518862495031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110176079/5000000000 : ℝ)|^8225 ≤ (13481132373229/100000000000000 : ℝ)^6177
        have hw : |(-1110176079/5000000000 : ℝ)|=(1110176079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397987993/10000000000 : ℝ)|^8225 ≤ (44000005111421/100000000000000 : ℝ)^6177
        have hw : |(5397987993/10000000000 : ℝ)|=(5397987993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260944021/10000000000 : ℝ)|^8225 ≤ (42518862495031/100000000000000 : ℝ)^6177
        have hw : |(5260944021/10000000000 : ℝ)|=(5260944021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s5_1 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345803239/10000000000 : ℝ)*x 0 + (-1144969521/5000000000 : ℝ)*x 1 + (5260943949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345803239/10000000000 : ℝ)^8225 ≤ (10858628859741/25000000000000 : ℝ)^6177 := by
    have hnat : (5345803239 : ℕ)^8225*25000000000000^6177 ≤ 10858628859741^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345803239 10000000000 10858628859741 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144969521/5000000000 : ℝ)^8225 ≤ (7023311409549/50000000000000 : ℝ)^6177 := by
    have hnat : (1144969521 : ℕ)^8225*50000000000000^6177 ≤ 7023311409549^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144969521 5000000000 7023311409549 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260943949/10000000000 : ℝ)^8225 ≤ (10629715430049/25000000000000 : ℝ)^6177 := by
    have hnat : (5260943949 : ℕ)^8225*25000000000000^6177 ≤ 10629715430049^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260943949 10000000000 10629715430049 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345803239/10000000000 : ℝ), (-1144969521/5000000000 : ℝ), (5260943949/10000000000 : ℝ)] ![(10858628859741/25000000000000 : ℝ), (7023311409549/50000000000000 : ℝ), (10629715430049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345803239/10000000000 : ℝ)|^8225 ≤ (10858628859741/25000000000000 : ℝ)^6177
        have hw : |(5345803239/10000000000 : ℝ)|=(5345803239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1144969521/5000000000 : ℝ)|^8225 ≤ (7023311409549/50000000000000 : ℝ)^6177
        have hw : |(-1144969521/5000000000 : ℝ)|=(1144969521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260943949/10000000000 : ℝ)|^8225 ≤ (10629715430049/25000000000000 : ℝ)^6177
        have hw : |(5260943949/10000000000 : ℝ)|=(5260943949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s5_2 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069160617/2000000000 : ℝ)*x 0 + (5260943629/10000000000 : ℝ)*x 1 + (-572484917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069160617/2000000000 : ℝ)^8225 ≤ (678664277701/1562500000000 : ℝ)^6177 := by
    have hnat : (1069160617 : ℕ)^8225*1562500000000^6177 ≤ 678664277701^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069160617 2000000000 678664277701 1562500000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260943629/10000000000 : ℝ)^8225 ≤ (42518858276489/100000000000000 : ℝ)^6177 := by
    have hnat : (5260943629 : ℕ)^8225*100000000000000^6177 ≤ 42518858276489^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260943629 10000000000 42518858276489 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572484917/2500000000 : ℝ)^8225 ≤ (2809325586431/20000000000000 : ℝ)^6177 := by
    have hnat : (572484917 : ℕ)^8225*20000000000000^6177 ≤ 2809325586431^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572484917 2500000000 2809325586431 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069160617/2000000000 : ℝ), (5260943629/10000000000 : ℝ), (-572484917/2500000000 : ℝ)] ![(678664277701/1562500000000 : ℝ), (42518858276489/100000000000000 : ℝ), (2809325586431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069160617/2000000000 : ℝ)|^8225 ≤ (678664277701/1562500000000 : ℝ)^6177
        have hw : |(1069160617/2000000000 : ℝ)|=(1069160617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260943629/10000000000 : ℝ)|^8225 ≤ (42518858276489/100000000000000 : ℝ)^6177
        have hw : |(5260943629/10000000000 : ℝ)|=(5260943629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-572484917/2500000000 : ℝ)|^8225 ≤ (2809325586431/20000000000000 : ℝ)^6177
        have hw : |(-572484917/2500000000 : ℝ)|=(572484917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s5_3 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1095062517/2500000000 : ℝ)*x 0 + (424893729/1000000000 : ℝ)*x 1 + (451571189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095062517/2500000000 : ℝ)^8225 ≤ (16657390346427/50000000000000 : ℝ)^6177 := by
    have hnat : (1095062517 : ℕ)^8225*50000000000000^6177 ≤ 16657390346427^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095062517 2500000000 16657390346427 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424893729/1000000000 : ℝ)^8225 ≤ (31991582255189/100000000000000 : ℝ)^6177 := by
    have hnat : (424893729 : ℕ)^8225*100000000000000^6177 ≤ 31991582255189^6177*1000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424893729 1000000000 31991582255189 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451571189/1000000000 : ℝ)^8225 ≤ (8673409260563/25000000000000 : ℝ)^6177 := by
    have hnat : (451571189 : ℕ)^8225*25000000000000^6177 ≤ 8673409260563^6177*1000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451571189 1000000000 8673409260563 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1095062517/2500000000 : ℝ), (424893729/1000000000 : ℝ), (451571189/1000000000 : ℝ)] ![(16657390346427/50000000000000 : ℝ), (31991582255189/100000000000000 : ℝ), (8673409260563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1095062517/2500000000 : ℝ)|^8225 ≤ (16657390346427/50000000000000 : ℝ)^6177
        have hw : |(1095062517/2500000000 : ℝ)|=(1095062517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424893729/1000000000 : ℝ)|^8225 ≤ (31991582255189/100000000000000 : ℝ)^6177
        have hw : |(424893729/1000000000 : ℝ)|=(424893729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451571189/1000000000 : ℝ)|^8225 ≤ (8673409260563/25000000000000 : ℝ)^6177
        have hw : |(451571189/1000000000 : ℝ)|=(451571189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s5_4 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220358187/10000000000 : ℝ)*x 0 + (5261302239/10000000000 : ℝ)*x 1 + (2698814159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220358187/10000000000 : ℝ)^8225 ≤ (1685147639473/12500000000000 : ℝ)^6177 := by
    have hnat : (2220358187 : ℕ)^8225*12500000000000^6177 ≤ 1685147639473^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220358187 10000000000 1685147639473 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261302239/10000000000 : ℝ)^8225 ≤ (42522717532191/100000000000000 : ℝ)^6177 := by
    have hnat : (5261302239 : ℕ)^8225*100000000000000^6177 ≤ 42522717532191^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261302239 10000000000 42522717532191 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698814159/5000000000 : ℝ)^8225 ≤ (10999025334567/25000000000000 : ℝ)^6177 := by
    have hnat : (2698814159 : ℕ)^8225*25000000000000^6177 ≤ 10999025334567^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698814159 5000000000 10999025334567 25000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220358187/10000000000 : ℝ), (5261302239/10000000000 : ℝ), (2698814159/5000000000 : ℝ)] ![(1685147639473/12500000000000 : ℝ), (42522717532191/100000000000000 : ℝ), (10999025334567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220358187/10000000000 : ℝ)|^8225 ≤ (1685147639473/12500000000000 : ℝ)^6177
        have hw : |(-2220358187/10000000000 : ℝ)|=(2220358187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261302239/10000000000 : ℝ)|^8225 ≤ (42522717532191/100000000000000 : ℝ)^6177
        have hw : |(5261302239/10000000000 : ℝ)|=(5261302239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698814159/5000000000 : ℝ)|^8225 ≤ (10999025334567/25000000000000 : ℝ)^6177
        have hw : |(2698814159/5000000000 : ℝ)|=(2698814159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s5_5 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311378569/10000000000 : ℝ)*x 0 + (-2153256369/10000000000 : ℝ)*x 1 + (5397628261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311378569/10000000000 : ℝ)^8225 ≤ (43062478925893/100000000000000 : ℝ)^6177 := by
    have hnat : (5311378569 : ℕ)^8225*100000000000000^6177 ≤ 43062478925893^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311378569 10000000000 43062478925893 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153256369/10000000000 : ℝ)^8225 ≤ (12941420344313/100000000000000 : ℝ)^6177 := by
    have hnat : (2153256369 : ℕ)^8225*100000000000000^6177 ≤ 12941420344313^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153256369 10000000000 12941420344313 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397628261/10000000000 : ℝ)^8225 ≤ (43996100719619/100000000000000 : ℝ)^6177 := by
    have hnat : (5397628261 : ℕ)^8225*100000000000000^6177 ≤ 43996100719619^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397628261 10000000000 43996100719619 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311378569/10000000000 : ℝ), (-2153256369/10000000000 : ℝ), (5397628261/10000000000 : ℝ)] ![(43062478925893/100000000000000 : ℝ), (12941420344313/100000000000000 : ℝ), (43996100719619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311378569/10000000000 : ℝ)|^8225 ≤ (43062478925893/100000000000000 : ℝ)^6177
        have hw : |(5311378569/10000000000 : ℝ)|=(5311378569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153256369/10000000000 : ℝ)|^8225 ≤ (12941420344313/100000000000000 : ℝ)^6177
        have hw : |(-2153256369/10000000000 : ℝ)|=(2153256369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397628261/10000000000 : ℝ)|^8225 ≤ (43996100719619/100000000000000 : ℝ)^6177
        have hw : |(5397628261/10000000000 : ℝ)|=(5397628261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s5_6 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311378981/10000000000 : ℝ)*x 0 + (1349407039/2500000000 : ℝ)*x 1 + (-430651191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311378981/10000000000 : ℝ)^8225 ≤ (21531241686857/50000000000000 : ℝ)^6177 := by
    have hnat : (5311378981 : ℕ)^8225*50000000000000^6177 ≤ 21531241686857^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311378981 10000000000 21531241686857 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349407039/2500000000 : ℝ)^8225 ≤ (21998049790001/50000000000000 : ℝ)^6177 := by
    have hnat : (1349407039 : ℕ)^8225*50000000000000^6177 ≤ 21998049790001^6177*2500000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349407039 2500000000 21998049790001 50000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430651191/2000000000 : ℝ)^8225 ≤ (2588283406227/20000000000000 : ℝ)^6177 := by
    have hnat : (430651191 : ℕ)^8225*20000000000000^6177 ≤ 2588283406227^6177*2000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430651191 2000000000 2588283406227 20000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311378981/10000000000 : ℝ), (1349407039/2500000000 : ℝ), (-430651191/2000000000 : ℝ)] ![(21531241686857/50000000000000 : ℝ), (21998049790001/50000000000000 : ℝ), (2588283406227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311378981/10000000000 : ℝ)|^8225 ≤ (21531241686857/50000000000000 : ℝ)^6177
        have hw : |(5311378981/10000000000 : ℝ)|=(5311378981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349407039/2500000000 : ℝ)|^8225 ≤ (21998049790001/50000000000000 : ℝ)^6177
        have hw : |(1349407039/2500000000 : ℝ)|=(1349407039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430651191/2000000000 : ℝ)|^8225 ≤ (2588283406227/20000000000000 : ℝ)^6177
        have hw : |(-430651191/2000000000 : ℝ)|=(430651191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1032_s5_7 (p : ℝ) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4380260809/10000000000 : ℝ)*x 0 + (4515015081/10000000000 : ℝ)*x 1 + (2124818711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380260809/10000000000 : ℝ)^8225 ≤ (333148894709/1000000000000 : ℝ)^6177 := by
    have hnat : (4380260809 : ℕ)^8225*1000000000000^6177 ≤ 333148894709^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380260809 10000000000 333148894709 1000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515015081/10000000000 : ℝ)^8225 ≤ (4335813595689/12500000000000 : ℝ)^6177 := by
    have hnat : (4515015081 : ℕ)^8225*12500000000000^6177 ≤ 4335813595689^6177*10000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515015081 10000000000 4335813595689 12500000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124818711/5000000000 : ℝ)^8225 ≤ (31998601744137/100000000000000 : ℝ)^6177 := by
    have hnat : (2124818711 : ℕ)^8225*100000000000000^6177 ≤ 31998601744137^6177*5000000000^8225 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124818711 5000000000 31998601744137 100000000000000 8225 6177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8225/2048 : ℝ)) 8225 6177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380260809/10000000000 : ℝ), (4515015081/10000000000 : ℝ), (2124818711/5000000000 : ℝ)] ![(333148894709/1000000000000 : ℝ), (4335813595689/12500000000000 : ℝ), (31998601744137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380260809/10000000000 : ℝ)|^8225 ≤ (333148894709/1000000000000 : ℝ)^6177
        have hw : |(4380260809/10000000000 : ℝ)|=(4380260809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515015081/10000000000 : ℝ)|^8225 ≤ (4335813595689/12500000000000 : ℝ)^6177
        have hw : |(4515015081/10000000000 : ℝ)|=(4515015081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124818711/5000000000 : ℝ)|^8225 ≤ (31998601744137/100000000000000 : ℝ)^6177
        have hw : |(2124818711/5000000000 : ℝ)|=(2124818711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1032_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2809/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2737/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2737/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2737/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2737/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2737/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2737/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2737/25000 : ℝ) ^ (257/64 : ℝ) ≤ (1734757501006409/12500000000000000000 : ℝ) := by
    have hpowers : (2737/25000 : ℝ)^257 ≤ (1734757501006409/12500000000000000000 : ℝ)^64 := by
      have hnat : (2737 : ℕ)^257*12500000000000000000^64 ≤ 1734757501006409^64*25000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2737 25000 1734757501006409 12500000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2737/25000 : ℝ)) (X := (1734757501006409/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14249/100000 : ℝ) ^ (257/64 : ℝ) ≤ (19993343670717477/50000000000000000000 : ℝ) := by
    have hpowers : (14249/100000 : ℝ)^257 ≤ (19993343670717477/50000000000000000000 : ℝ)^64 := by
      have hnat : (14249 : ℕ)^257*50000000000000000000^64 ≤ 19993343670717477^64*100000^257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14249 100000 19993343670717477 50000000000000000000 257 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14249/100000 : ℝ)) (X := (19993343670717477/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251734757501006409/6250000000000000000 : ℝ) ≤ (10000691130962909/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (6251734757501006409/6250000000000000000 : ℝ)^64 ≤ (10000691130962909/10000000000000000 : ℝ)^257 := by
      have hnat : (6251734757501006409 : ℕ)^64*10000000000000000^257 ≤ 10000691130962909^257*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251734757501006409 6250000000000000000 10000691130962909 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000691130962909/10000000000000000 : ℝ)) (X := (6251734757501006409/6250000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026932373674743113/50000000000000000000 : ℝ) ≤ (10001341107707271/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (50026932373674743113/50000000000000000000 : ℝ)^64 ≤ (10001341107707271/10000000000000000 : ℝ)^257 := by
      have hnat : (50026932373674743113 : ℕ)^64*10000000000000000^257 ≤ 10001341107707271^257*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026932373674743113 50000000000000000000 10001341107707271 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001341107707271/10000000000000000 : ℝ)) (X := (50026932373674743113/50000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019993343670717477/25000000000000000000 : ℝ) ≤ (10001991084451633/10000000000000000 : ℝ) ^ (257/64 : ℝ) := by
    have hpowers : (25019993343670717477/25000000000000000000 : ℝ)^64 ≤ (10001991084451633/10000000000000000 : ℝ)^257 := by
      have hnat : (25019993343670717477 : ℕ)^64*10000000000000000^257 ≤ 10001991084451633^257*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019993343670717477 25000000000000000000 10001991084451633 10000000000000000 64 257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001991084451633/10000000000000000 : ℝ)) (X := (25019993343670717477/25000000000000000000 : ℝ)) (by norm_num) 257 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1734757501006409/12500000000000000000 : ℝ) ≤ ((32998049532514012257/33010000000000000000 : ℝ)+2*(324988372181/165050000000000 : ℝ)*(2737/25000 : ℝ))^(257/64 : ℝ) := by
    rw [show (32998049532514012257/33010000000000000000 : ℝ)+2*(324988372181/165050000000000 : ℝ)*(2737/25000 : ℝ)=(10000691130962909/10000000000000000 : ℝ) by norm_num, show 1+2*(1734757501006409/12500000000000000000 : ℝ)=(6251734757501006409/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19993343670717477/50000000000000000000 : ℝ)+(1734757501006409/12500000000000000000 : ℝ) ≤ ((32998049532514012257/33010000000000000000 : ℝ)+(324988372181/165050000000000 : ℝ)*((14249/100000 : ℝ)+(2737/25000 : ℝ)))^(257/64 : ℝ) := by
    rw [show (32998049532514012257/33010000000000000000 : ℝ)+(324988372181/165050000000000 : ℝ)*((14249/100000 : ℝ)+(2737/25000 : ℝ))=(10001341107707271/10000000000000000 : ℝ) by norm_num, show 1+(19993343670717477/50000000000000000000 : ℝ)+(1734757501006409/12500000000000000000 : ℝ)=(50026932373674743113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19993343670717477/50000000000000000000 : ℝ) ≤ ((32998049532514012257/33010000000000000000 : ℝ)+2*(324988372181/165050000000000 : ℝ)*(14249/100000 : ℝ))^(257/64 : ℝ) := by
    rw [show (32998049532514012257/33010000000000000000 : ℝ)+2*(324988372181/165050000000000 : ℝ)*(14249/100000 : ℝ)=(10001991084451633/10000000000000000 : ℝ) by norm_num, show 1+2*(19993343670717477/50000000000000000000 : ℝ)=(25019993343670717477/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32998049532514012257/33010000000000000000 : ℝ)*(X 1 0+X 2 0)+(324988372181/165050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (2737/25000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32998049532514012257/33010000000000000000 : ℝ)) (alpha := (324988372181/165050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32998049532514012257/33010000000000000000 : ℝ)*(X 0 1+X 2 1)+(324988372181/165050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (2737/25000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32998049532514012257/33010000000000000000 : ℝ)) (alpha := (324988372181/165050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32998049532514012257/33010000000000000000 : ℝ)*(X 0 2+X 1 2)+(324988372181/165050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (257/64 : ℝ)) (lo := (2737/25000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32998049532514012257/33010000000000000000 : ℝ)) (alpha := (324988372181/165050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1110176079/5000000000 : ℝ)*X 0 0+(5397987993/10000000000 : ℝ)*X 0 1+(5260944021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345803239/10000000000 : ℝ)*X 1 0+(-1144969521/5000000000 : ℝ)*X 1 1+(5260943949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069160617/2000000000 : ℝ)*X 2 0+(5260943629/10000000000 : ℝ)*X 2 1+(-572484917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1095062517/2500000000 : ℝ)*X 0 0+(424893729/1000000000 : ℝ)*X 0 1+(451571189/1000000000 : ℝ)*X 0 2+(1095062517/2500000000 : ℝ)*X 1 0+(424893729/1000000000 : ℝ)*X 1 1+(451571189/1000000000 : ℝ)*X 1 2+(1095062517/2500000000 : ℝ)*X 2 0+(424893729/1000000000 : ℝ)*X 2 1+(451571189/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2220358187/10000000000 : ℝ)*X 0 0+(5261302239/10000000000 : ℝ)*X 0 1+(2698814159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311378569/10000000000 : ℝ)*X 1 0+(-2153256369/10000000000 : ℝ)*X 1 1+(5397628261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311378981/10000000000 : ℝ)*X 2 0+(1349407039/2500000000 : ℝ)*X 2 1+(-430651191/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4380260809/10000000000 : ℝ)*X 0 0+(4515015081/10000000000 : ℝ)*X 0 1+(2124818711/5000000000 : ℝ)*X 0 2+(4380260809/10000000000 : ℝ)*X 1 0+(4515015081/10000000000 : ℝ)*X 1 1+(2124818711/5000000000 : ℝ)*X 1 2+(4380260809/10000000000 : ℝ)*X 2 0+(4515015081/10000000000 : ℝ)*X 2 1+(2124818711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1032_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (422774779217240251880458977/1650500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1280003139/100000000000000 : ℝ)*(base19) + (1288094931/100000000000000 : ℝ)*(base23) + (40914409/25000000000000 : ℝ)*(lower4) + (37015377/10000000000000 : ℝ)*(lower5) + (5522778584653013/100000000000000 : ℝ)*(major0) + (5522778584653013/100000000000000 : ℝ)*(major1) + (5522778584653013/100000000000000 : ℝ)*(major2) + (7296992205078853/100000000000000 : ℝ)*(sp0) + (3648515730485189/50000000000000 : ℝ)*(sp1) + (7297017811961113/100000000000000 : ℝ)*(sp2) + (1874250822838601/50000000000000 : ℝ)*(sp3) + (5066986833/12500000000000 : ℝ)*(sp4) + (426278671/3125000000000 : ℝ)*(sp6) + (22774116979/100000000000000 : ℝ)*(sp7) + (3748524419794181/100000000000000 : ℝ)*(f.failure) + (1824258185243379/25000000000000 : ℝ)*(f.sum) + (49620578203819/16505000000000000000000000000 : ℝ)*base66 + (23076620397759419659/3301000000000000000000000000000000 : ℝ)*base68 + (14508184736161580341/3301000000000000000000000000000000 : ℝ)*base69 + (35516814609255580341/3301000000000000000000000000000000 : ℝ)*base71 + (25062430888191/16505000000000000000000000000 : ℝ)*base73 + (19750305908404580341/3301000000000000000000000000000000 : ℝ)*base75 + (34848738299539419659/3301000000000000000000000000000000 : ℝ)*base78 + (74999139779056580341/3301000000000000000000000000000000 : ℝ)*base79 + (3913658152917/2063125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (59109511/10000000000000000000000 : ℝ)*base90 + (59109511/10000000000000000000000 : ℝ)*base92 + (59109511/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10627560996313121224114898511/1650500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24741651/10000000000000 : ℝ)*(base8) + (57976671/100000000000000 : ℝ)*(base21) + (185707941/100000000000000 : ℝ)*(base29) + (357264139/100000000000000 : ℝ)*(upper4) + (43718757/100000000000000 : ℝ)*(upper5) + (5551797503669477/100000000000000 : ℝ)*(major0) + (2775898844688709/50000000000000 : ℝ)*(major1) + (2775898844688709/50000000000000 : ℝ)*(major2) + (297692337/50000000000000 : ℝ)*(sp0) + (4047115479/50000000000000 : ℝ)*(sp2) + (1833843376894161/25000000000000 : ℝ)*(sp4) + (114615221322967/1562500000000 : ℝ)*(sp5) + (3667683006231129/50000000000000 : ℝ)*(sp6) + (942055203435957/25000000000000 : ℝ)*(sp7) + (942055203435957/25000000000000 : ℝ)*(f.failure) + (1833843587594457/25000000000000 : ℝ)*(f.sum) + (163430772576207/2063125000000000000000000000 : ℝ)*base65 + (13550459881891693787/1650500000000000000000000000000000 : ℝ)*base68 + (29172236227839693787/1650500000000000000000000000000000 : ℝ)*base70 + (169267936663062379589/3301000000000000000000000000000000 : ℝ)*base71 + (17611349074597/3301000000000000000000000000 : ℝ)*base74 + (7369582964017206213/1650500000000000000000000000000000 : ℝ)*base75 + (13813698544006379589/3301000000000000000000000000000000 : ℝ)*base77 + (2894937132439793787/1650500000000000000000000000000000 : ℝ)*base80 + (1400434128083/3301000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3805033/2500000000000000000000 : ℝ)*base89 + (3805033/2500000000000000000000 : ℝ)*base91 + (3805033/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1032_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1032_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1032_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16851/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4273/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1032_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1032_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1032_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (257/64 : ℝ) ≤ p) (hpb : p ≤ (8225/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147332069/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16851/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4273/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1032_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
