-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1624_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:27.742688+00:00
-- url     : https://prove2.me/submissions/caa009ba-cf83-4ecd-b46c-0c0fdf6a3cec

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
theorem support_rectangle_w1624_s0_0 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-30787939/200000000 : ℝ)*x 0 + (5818456393/10000000000 : ℝ)*x 1 + (612915197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30787939/200000000 : ℝ)^4815 ≤ (4643154318249/50000000000000 : ℝ)^3791 := by
    have hnat : (30787939 : ℕ)^4815*50000000000000^3791 ≤ 4643154318249^3791*200000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30787939 200000000 4643154318249 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5818456393/10000000000 : ℝ)^4815 ≤ (6283320624437/12500000000000 : ℝ)^3791 := by
    have hnat : (5818456393 : ℕ)^4815*12500000000000^3791 ≤ 6283320624437^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5818456393 10000000000 6283320624437 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612915197/1250000000 : ℝ)^4815 ≤ (40447126353927/100000000000000 : ℝ)^3791 := by
    have hnat : (612915197 : ℕ)^4815*100000000000000^3791 ≤ 40447126353927^3791*1250000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612915197 1250000000 40447126353927 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-30787939/200000000 : ℝ), (5818456393/10000000000 : ℝ), (612915197/1250000000 : ℝ)] ![(4643154318249/50000000000000 : ℝ), (6283320624437/12500000000000 : ℝ), (40447126353927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-30787939/200000000 : ℝ)|^4815 ≤ (4643154318249/50000000000000 : ℝ)^3791
        have hw : |(-30787939/200000000 : ℝ)|=(30787939/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5818456393/10000000000 : ℝ)|^4815 ≤ (6283320624437/12500000000000 : ℝ)^3791
        have hw : |(5818456393/10000000000 : ℝ)|=(5818456393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(612915197/1250000000 : ℝ)|^4815 ≤ (40447126353927/100000000000000 : ℝ)^3791
        have hw : |(612915197/1250000000 : ℝ)|=(612915197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s0_1 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5447983139/10000000000 : ℝ)*x 0 + (-2044509331/10000000000 : ℝ)*x 1 + (4903322323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5447983139/10000000000 : ℝ)^4815 ≤ (23118491631103/50000000000000 : ℝ)^3791 := by
    have hnat : (5447983139 : ℕ)^4815*50000000000000^3791 ≤ 23118491631103^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447983139 10000000000 23118491631103 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044509331/10000000000 : ℝ)^4815 ≤ (13315882543363/100000000000000 : ℝ)^3791 := by
    have hnat : (2044509331 : ℕ)^4815*100000000000000^3791 ≤ 13315882543363^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044509331 10000000000 13315882543363 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4903322323/10000000000 : ℝ)^4815 ≤ (20223567090149/50000000000000 : ℝ)^3791 := by
    have hnat : (4903322323 : ℕ)^4815*50000000000000^3791 ≤ 20223567090149^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4903322323 10000000000 20223567090149 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5447983139/10000000000 : ℝ), (-2044509331/10000000000 : ℝ), (4903322323/10000000000 : ℝ)] ![(23118491631103/50000000000000 : ℝ), (13315882543363/100000000000000 : ℝ), (20223567090149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5447983139/10000000000 : ℝ)|^4815 ≤ (23118491631103/50000000000000 : ℝ)^3791
        have hw : |(5447983139/10000000000 : ℝ)|=(5447983139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044509331/10000000000 : ℝ)|^4815 ≤ (13315882543363/100000000000000 : ℝ)^3791
        have hw : |(-2044509331/10000000000 : ℝ)|=(2044509331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4903322323/10000000000 : ℝ)|^4815 ≤ (20223567090149/50000000000000 : ℝ)^3791
        have hw : |(4903322323/10000000000 : ℝ)|=(4903322323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s0_2 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2723991441/5000000000 : ℝ)*x 0 + (980664391/2000000000 : ℝ)*x 1 + (-511127533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2723991441/5000000000 : ℝ)^4815 ≤ (4623698049189/10000000000000 : ℝ)^3791 := by
    have hnat : (2723991441 : ℕ)^4815*10000000000000^3791 ≤ 4623698049189^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723991441 5000000000 4623698049189 10000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980664391/2000000000 : ℝ)^4815 ≤ (157996602831/390625000000 : ℝ)^3791 := by
    have hnat : (980664391 : ℕ)^4815*390625000000^3791 ≤ 157996602831^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980664391 2000000000 157996602831 390625000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511127533/2500000000 : ℝ)^4815 ≤ (1664486146179/12500000000000 : ℝ)^3791 := by
    have hnat : (511127533 : ℕ)^4815*12500000000000^3791 ≤ 1664486146179^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511127533 2500000000 1664486146179 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2723991441/5000000000 : ℝ), (980664391/2000000000 : ℝ), (-511127533/2500000000 : ℝ)] ![(4623698049189/10000000000000 : ℝ), (157996602831/390625000000 : ℝ), (1664486146179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2723991441/5000000000 : ℝ)|^4815 ≤ (4623698049189/10000000000000 : ℝ)^3791
        have hw : |(2723991441/5000000000 : ℝ)|=(2723991441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(980664391/2000000000 : ℝ)|^4815 ≤ (157996602831/390625000000 : ℝ)^3791
        have hw : |(980664391/2000000000 : ℝ)|=(980664391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511127533/2500000000 : ℝ)|^4815 ≤ (1664486146179/12500000000000 : ℝ)^3791
        have hw : |(-511127533/2500000000 : ℝ)|=(511127533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s0_3 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2051484007/5000000000 : ℝ)*x 0 + (3076806817/10000000000 : ℝ)*x 1 + (1073423639/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051484007/5000000000 : ℝ)^4815 ≤ (8063632943719/25000000000000 : ℝ)^3791 := by
    have hnat : (2051484007 : ℕ)^4815*25000000000000^3791 ≤ 8063632943719^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051484007 5000000000 8063632943719 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3076806817/10000000000 : ℝ)^4815 ≤ (22378410081033/100000000000000 : ℝ)^3791 := by
    have hnat : (3076806817 : ℕ)^4815*100000000000000^3791 ≤ 22378410081033^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3076806817 10000000000 22378410081033 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073423639/2000000000 : ℝ)^4815 ≤ (45367058134031/100000000000000 : ℝ)^3791 := by
    have hnat : (1073423639 : ℕ)^4815*100000000000000^3791 ≤ 45367058134031^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073423639 2000000000 45367058134031 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2051484007/5000000000 : ℝ), (3076806817/10000000000 : ℝ), (1073423639/2000000000 : ℝ)] ![(8063632943719/25000000000000 : ℝ), (22378410081033/100000000000000 : ℝ), (45367058134031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2051484007/5000000000 : ℝ)|^4815 ≤ (8063632943719/25000000000000 : ℝ)^3791
        have hw : |(2051484007/5000000000 : ℝ)|=(2051484007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3076806817/10000000000 : ℝ)|^4815 ≤ (22378410081033/100000000000000 : ℝ)^3791
        have hw : |(3076806817/10000000000 : ℝ)|=(3076806817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1073423639/2000000000 : ℝ)|^4815 ≤ (45367058134031/100000000000000 : ℝ)^3791
        have hw : |(1073423639/2000000000 : ℝ)|=(1073423639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s0_4 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-385501503/2500000000 : ℝ)*x 0 + (2463164587/5000000000 : ℝ)*x 1 + (2897319367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385501503/2500000000 : ℝ)^4815 ≤ (4653151757213/50000000000000 : ℝ)^3791 := by
    have hnat : (385501503 : ℕ)^4815*50000000000000^3791 ≤ 4653151757213^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385501503 2500000000 4653151757213 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463164587/5000000000 : ℝ)^4815 ≤ (40688331130039/100000000000000 : ℝ)^3791 := by
    have hnat : (2463164587 : ℕ)^4815*100000000000000^3791 ≤ 40688331130039^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463164587 5000000000 40688331130039 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2897319367/5000000000 : ℝ)^4815 ≤ (50005365340547/100000000000000 : ℝ)^3791 := by
    have hnat : (2897319367 : ℕ)^4815*100000000000000^3791 ≤ 50005365340547^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897319367 5000000000 50005365340547 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385501503/2500000000 : ℝ), (2463164587/5000000000 : ℝ), (2897319367/5000000000 : ℝ)] ![(4653151757213/50000000000000 : ℝ), (40688331130039/100000000000000 : ℝ), (50005365340547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385501503/2500000000 : ℝ)|^4815 ≤ (4653151757213/50000000000000 : ℝ)^3791
        have hw : |(-385501503/2500000000 : ℝ)|=(385501503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2463164587/5000000000 : ℝ)|^4815 ≤ (40688331130039/100000000000000 : ℝ)^3791
        have hw : |(2463164587/5000000000 : ℝ)|=(2463164587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2897319367/5000000000 : ℝ)|^4815 ≤ (50005365340547/100000000000000 : ℝ)^3791
        have hw : |(2897319367/5000000000 : ℝ)|=(2897319367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s0_5 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039619261/2000000000 : ℝ)*x 0 + (-288298227/2500000000 : ℝ)*x 1 + (289731937/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039619261/2000000000 : ℝ)^4815 ≤ (43560219288069/100000000000000 : ℝ)^3791 := by
    have hnat : (1039619261 : ℕ)^4815*100000000000000^3791 ≤ 43560219288069^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039619261 2000000000 43560219288069 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288298227/2500000000 : ℝ)^4815 ≤ (3217207644437/50000000000000 : ℝ)^3791 := by
    have hnat : (288298227 : ℕ)^4815*50000000000000^3791 ≤ 3217207644437^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288298227 2500000000 3217207644437 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289731937/500000000 : ℝ)^4815 ≤ (5000536540631/10000000000000 : ℝ)^3791 := by
    have hnat : (289731937 : ℕ)^4815*10000000000000^3791 ≤ 5000536540631^3791*500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289731937 500000000 5000536540631 10000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039619261/2000000000 : ℝ), (-288298227/2500000000 : ℝ), (289731937/500000000 : ℝ)] ![(43560219288069/100000000000000 : ℝ), (3217207644437/50000000000000 : ℝ), (5000536540631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039619261/2000000000 : ℝ)|^4815 ≤ (43560219288069/100000000000000 : ℝ)^3791
        have hw : |(1039619261/2000000000 : ℝ)|=(1039619261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-288298227/2500000000 : ℝ)|^4815 ≤ (3217207644437/50000000000000 : ℝ)^3791
        have hw : |(-288298227/2500000000 : ℝ)|=(288298227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(289731937/500000000 : ℝ)|^4815 ≤ (5000536540631/10000000000000 : ℝ)^3791
        have hw : |(289731937/500000000 : ℝ)|=(289731937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s0_6 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039619261/2000000000 : ℝ)*x 0 + (1448659737/2500000000 : ℝ)*x 1 + (-1153192587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039619261/2000000000 : ℝ)^4815 ≤ (43560219288069/100000000000000 : ℝ)^3791 := by
    have hnat : (1039619261 : ℕ)^4815*100000000000000^3791 ≤ 43560219288069^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039619261 2000000000 43560219288069 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1448659737/2500000000 : ℝ)^4815 ≤ (50005367686107/100000000000000 : ℝ)^3791 := by
    have hnat : (1448659737 : ℕ)^4815*100000000000000^3791 ≤ 50005367686107^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448659737 2500000000 50005367686107 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153192587/10000000000 : ℝ)^4815 ≤ (1286882602803/20000000000000 : ℝ)^3791 := by
    have hnat : (1153192587 : ℕ)^4815*20000000000000^3791 ≤ 1286882602803^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153192587 10000000000 1286882602803 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039619261/2000000000 : ℝ), (1448659737/2500000000 : ℝ), (-1153192587/10000000000 : ℝ)] ![(43560219288069/100000000000000 : ℝ), (50005367686107/100000000000000 : ℝ), (1286882602803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039619261/2000000000 : ℝ)|^4815 ≤ (43560219288069/100000000000000 : ℝ)^3791
        have hw : |(1039619261/2000000000 : ℝ)|=(1039619261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1448659737/2500000000 : ℝ)|^4815 ≤ (50005367686107/100000000000000 : ℝ)^3791
        have hw : |(1448659737/2500000000 : ℝ)|=(1448659737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1153192587/10000000000 : ℝ)|^4815 ≤ (1286882602803/20000000000000 : ℝ)^3791
        have hw : |(-1153192587/10000000000 : ℝ)|=(1153192587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s0_7 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4109498659/10000000000 : ℝ)*x 0 + (5309534699/10000000000 : ℝ)*x 1 + (3136416149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109498659/10000000000 : ℝ)^4815 ≤ (8079938083117/25000000000000 : ℝ)^3791 := by
    have hnat : (4109498659 : ℕ)^4815*25000000000000^3791 ≤ 8079938083117^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109498659 10000000000 8079938083117 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5309534699/10000000000 : ℝ)^4815 ≤ (44749740639087/100000000000000 : ℝ)^3791 := by
    have hnat : (5309534699 : ℕ)^4815*100000000000000^3791 ≤ 44749740639087^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309534699 10000000000 44749740639087 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3136416149/10000000000 : ℝ)^4815 ≤ (11465253507333/50000000000000 : ℝ)^3791 := by
    have hnat : (3136416149 : ℕ)^4815*50000000000000^3791 ≤ 11465253507333^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136416149 10000000000 11465253507333 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109498659/10000000000 : ℝ), (5309534699/10000000000 : ℝ), (3136416149/10000000000 : ℝ)] ![(8079938083117/25000000000000 : ℝ), (44749740639087/100000000000000 : ℝ), (11465253507333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109498659/10000000000 : ℝ)|^4815 ≤ (8079938083117/25000000000000 : ℝ)^3791
        have hw : |(4109498659/10000000000 : ℝ)|=(4109498659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5309534699/10000000000 : ℝ)|^4815 ≤ (44749740639087/100000000000000 : ℝ)^3791
        have hw : |(5309534699/10000000000 : ℝ)|=(5309534699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3136416149/10000000000 : ℝ)|^4815 ≤ (11465253507333/50000000000000 : ℝ)^3791
        have hw : |(3136416149/10000000000 : ℝ)|=(3136416149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1624_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4321/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5981/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4811/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4811 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4811*1^1024 ≤ 0^1024*1^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4811/1024 : ℝ) ≤ (54005930661342451/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4811 ≤ (54005930661342451/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4811*4000000000000000000^1024 ≤ 54005930661342451^1024*5^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 54005930661342451 4000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (54005930661342451/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4811 := by
      have hnat : (1 : ℕ)^1024*1^4811 ≤ 1^4811*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4054005930661342451/4000000000000000000 : ℝ) ≤ (5014292908499789/5000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (4054005930661342451/4000000000000000000 : ℝ)^1024 ≤ (5014292908499789/5000000000000000 : ℝ)^4811 := by
      have hnat : (4054005930661342451 : ℕ)^1024*5000000000000000^4811 ≤ 5014292908499789^4811*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4054005930661342451 4000000000000000000 5014292908499789 5000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014292908499789/5000000000000000 : ℝ)) (X := (4054005930661342451/4000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2054005930661342451/2000000000000000000 : ℝ) ≤ (2514292908499789/2500000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (2054005930661342451/2000000000000000000 : ℝ)^1024 ≤ (2514292908499789/2500000000000000 : ℝ)^4811 := by
      have hnat : (2054005930661342451 : ℕ)^1024*2500000000000000^4811 ≤ 2514292908499789^4811*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2054005930661342451 2000000000000000000 2514292908499789 2500000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514292908499789/2500000000000000 : ℝ)) (X := (2054005930661342451/2000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14292908499789/2000000000000000 : ℝ)*(0 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14292908499789/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54005930661342451/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14292908499789/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4811/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14292908499789/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5014292908499789/5000000000000000 : ℝ) by norm_num, show 1+(54005930661342451/4000000000000000000 : ℝ)+(0 : ℝ)=(4054005930661342451/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54005930661342451/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14292908499789/2000000000000000 : ℝ)*(2/5 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14292908499789/2000000000000000 : ℝ)*(2/5 : ℝ)=(2514292908499789/2500000000000000 : ℝ) by norm_num, show 1+2*(54005930661342451/4000000000000000000 : ℝ)=(2054005930661342451/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14292908499789/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14292908499789/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14292908499789/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14292908499789/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14292908499789/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14292908499789/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-30787939/200000000 : ℝ)*X 0 0+(5818456393/10000000000 : ℝ)*X 0 1+(612915197/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5447983139/10000000000 : ℝ)*X 1 0+(-2044509331/10000000000 : ℝ)*X 1 1+(4903322323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2723991441/5000000000 : ℝ)*X 2 0+(980664391/2000000000 : ℝ)*X 2 1+(-511127533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2051484007/5000000000 : ℝ)*X 0 0+(3076806817/10000000000 : ℝ)*X 0 1+(1073423639/2000000000 : ℝ)*X 0 2+(2051484007/5000000000 : ℝ)*X 1 0+(3076806817/10000000000 : ℝ)*X 1 1+(1073423639/2000000000 : ℝ)*X 1 2+(2051484007/5000000000 : ℝ)*X 2 0+(3076806817/10000000000 : ℝ)*X 2 1+(1073423639/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-385501503/2500000000 : ℝ)*X 0 0+(2463164587/5000000000 : ℝ)*X 0 1+(2897319367/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1039619261/2000000000 : ℝ)*X 1 0+(-288298227/2500000000 : ℝ)*X 1 1+(289731937/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1039619261/2000000000 : ℝ)*X 2 0+(1448659737/2500000000 : ℝ)*X 2 1+(-1153192587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4109498659/10000000000 : ℝ)*X 0 0+(5309534699/10000000000 : ℝ)*X 0 1+(3136416149/10000000000 : ℝ)*X 0 2+(4109498659/10000000000 : ℝ)*X 1 0+(5309534699/10000000000 : ℝ)*X 1 1+(3136416149/10000000000 : ℝ)*X 1 2+(4109498659/10000000000 : ℝ)*X 2 0+(5309534699/10000000000 : ℝ)*X 2 1+(3136416149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (244780331972176377/50000000000000000000000 : ℝ) := by norm_num
    linear_combination (926582751/100000000000000 : ℝ)*(base19) + (440107287/50000000000000 : ℝ)*(base23) + (2516371/10000000000000 : ℝ)*(upper2) + (269971473/100000000000000 : ℝ)*(upper3) + (11170763/50000000000000 : ℝ)*(upper4) + (764684763880963/100000000000000 : ℝ)*(major0) + (764684763880963/100000000000000 : ℝ)*(major1) + (764684763880963/100000000000000 : ℝ)*(major2) + (1092740444859967/100000000000000 : ℝ)*(sp0) + (136592837939557/12500000000000 : ℝ)*(sp1) + (546371374942317/50000000000000 : ℝ)*(sp2) + (109155838940347/25000000000000 : ℝ)*(sp3) + (3185239241/100000000000000 : ℝ)*(sp4) + (2378714437/100000000000000 : ℝ)*(sp7) + (17465029379033/4000000000000 : ℝ)*(f.failure) + (136592953762401/12500000000000 : ℝ)*(f.sum) + (268719119316807/100000000000000000000000000000 : ℝ)*base65 + (1274707778183193/200000000000000000000000000000 : ℝ)*base68 + (864355625183193/200000000000000000000000000000 : ℝ)*base70 + (386021946816807/200000000000000000000000000000 : ℝ)*base71 + (267782345683193/100000000000000000000000000000 : ℝ)*base74 + (764136694416807/200000000000000000000000000000 : ℝ)*base75 + (655938013983193/200000000000000000000000000000 : ℝ)*base78 + (1578808479183193/200000000000000000000000000000 : ℝ)*base80 + (197027098116807/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (418429/80000000000000000000 : ℝ)*base89 + (418429/80000000000000000000 : ℝ)*base91 + (418429/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112241478900346300139661/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31826343/3125000000000 : ℝ)*(base19) + (545809021/50000000000000 : ℝ)*(base23) + (67383891/100000000000000 : ℝ)*(base39) + (134964529/100000000000000 : ℝ)*(upper3) + (199353273/100000000000000 : ℝ)*(upper5) + (402957757387631/50000000000000 : ℝ)*(major0) + (402957757387631/50000000000000 : ℝ)*(major1) + (201478861847843/25000000000000 : ℝ)*(major2) + (3298699839/100000000000000 : ℝ)*(sp1) + (3438441209/100000000000000 : ℝ)*(sp2) + (575831409434331/50000000000000 : ℝ)*(sp4) + (575829250862923/50000000000000 : ℝ)*(sp5) + (11516583561933/1000000000000 : ℝ)*(sp6) + (14380249801333/3125000000000 : ℝ)*(sp7) + (14380249801333/3125000000000 : ℝ)*(f.failure) + (143957860781569/12500000000000 : ℝ)*(f.sum) + (131110749920113/100000000000000000000000000000 : ℝ)*base65 + (112708229005127/50000000000000000000000000000 : ℝ)*base67 + (735067389509859/100000000000000000000000000000 : ℝ)*base69 + (95540917855127/50000000000000000000000000000 : ℝ)*base71 + (175858719220113/100000000000000000000000000000 : ℝ)*base73 + (1069854776609859/100000000000000000000000000000 : ℝ)*base75 + (649994040509859/100000000000000000000000000000 : ℝ)*base77 + (1414666700809859/100000000000000000000000000000 : ℝ)*base79 + (236559798090141/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (341671/62500000000000000000 : ℝ)*base90 + (341671/62500000000000000000 : ℝ)*base92 + (966671/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1624_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5981/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1624_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1624_s1_0 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1656439907/10000000000 : ℝ)*x 0 + (2758633373/5000000000 : ℝ)*x 1 + (1025737159/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656439907/10000000000 : ℝ)^4815 ≤ (10192120596651/100000000000000 : ℝ)^3791 := by
    have hnat : (1656439907 : ℕ)^4815*100000000000000^3791 ≤ 10192120596651^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656439907 10000000000 10192120596651 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758633373/5000000000 : ℝ)^4815 ≤ (46985100611449/100000000000000 : ℝ)^3791 := by
    have hnat : (2758633373 : ℕ)^4815*100000000000000^3791 ≤ 46985100611449^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758633373 5000000000 46985100611449 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025737159/2000000000 : ℝ)^4815 ≤ (42822778777039/100000000000000 : ℝ)^3791 := by
    have hnat : (1025737159 : ℕ)^4815*100000000000000^3791 ≤ 42822778777039^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025737159 2000000000 42822778777039 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1656439907/10000000000 : ℝ), (2758633373/5000000000 : ℝ), (1025737159/2000000000 : ℝ)] ![(10192120596651/100000000000000 : ℝ), (46985100611449/100000000000000 : ℝ), (42822778777039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1656439907/10000000000 : ℝ)|^4815 ≤ (10192120596651/100000000000000 : ℝ)^3791
        have hw : |(-1656439907/10000000000 : ℝ)|=(1656439907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758633373/5000000000 : ℝ)|^4815 ≤ (46985100611449/100000000000000 : ℝ)^3791
        have hw : |(2758633373/5000000000 : ℝ)|=(2758633373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025737159/2000000000 : ℝ)|^4815 ≤ (42822778777039/100000000000000 : ℝ)^3791
        have hw : |(1025737159/2000000000 : ℝ)|=(1025737159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s1_1 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214714471/400000000 : ℝ)*x 0 + (-464800867/2500000000 : ℝ)*x 1 + (5128685583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214714471/400000000 : ℝ)^4815 ≤ (45375041348403/100000000000000 : ℝ)^3791 := by
    have hnat : (214714471 : ℕ)^4815*100000000000000^3791 ≤ 45375041348403^3791*400000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214714471 400000000 45375041348403 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464800867/2500000000 : ℝ)^4815 ≤ (11802182112823/100000000000000 : ℝ)^3791 := by
    have hnat : (464800867 : ℕ)^4815*100000000000000^3791 ≤ 11802182112823^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464800867 2500000000 11802182112823 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128685583/10000000000 : ℝ)^4815 ≤ (5352847066097/12500000000000 : ℝ)^3791 := by
    have hnat : (5128685583 : ℕ)^4815*12500000000000^3791 ≤ 5352847066097^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128685583 10000000000 5352847066097 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214714471/400000000 : ℝ), (-464800867/2500000000 : ℝ), (5128685583/10000000000 : ℝ)] ![(45375041348403/100000000000000 : ℝ), (11802182112823/100000000000000 : ℝ), (5352847066097/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214714471/400000000 : ℝ)|^4815 ≤ (45375041348403/100000000000000 : ℝ)^3791
        have hw : |(214714471/400000000 : ℝ)|=(214714471/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-464800867/2500000000 : ℝ)|^4815 ≤ (11802182112823/100000000000000 : ℝ)^3791
        have hw : |(-464800867/2500000000 : ℝ)|=(464800867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128685583/10000000000 : ℝ)|^4815 ≤ (5352847066097/12500000000000 : ℝ)^3791
        have hw : |(5128685583/10000000000 : ℝ)|=(5128685583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s1_2 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367862169/10000000000 : ℝ)*x 0 + (5128685053/10000000000 : ℝ)*x 1 + (-46480091/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367862169/10000000000 : ℝ)^4815 ≤ (45375045578541/100000000000000 : ℝ)^3791 := by
    have hnat : (5367862169 : ℕ)^4815*100000000000000^3791 ≤ 45375045578541^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367862169 10000000000 45375045578541 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128685053/10000000000 : ℝ)^4815 ≤ (42822770908119/100000000000000 : ℝ)^3791 := by
    have hnat : (5128685053 : ℕ)^4815*100000000000000^3791 ≤ 42822770908119^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128685053 10000000000 42822770908119 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46480091/250000000 : ℝ)^4815 ≤ (11802183499599/100000000000000 : ℝ)^3791 := by
    have hnat : (46480091 : ℕ)^4815*100000000000000^3791 ≤ 11802183499599^3791*250000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46480091 250000000 11802183499599 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367862169/10000000000 : ℝ), (5128685053/10000000000 : ℝ), (-46480091/250000000 : ℝ)] ![(45375045578541/100000000000000 : ℝ), (42822770908119/100000000000000 : ℝ), (11802183499599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367862169/10000000000 : ℝ)|^4815 ≤ (45375045578541/100000000000000 : ℝ)^3791
        have hw : |(5367862169/10000000000 : ℝ)|=(5367862169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128685053/10000000000 : ℝ)|^4815 ≤ (42822770908119/100000000000000 : ℝ)^3791
        have hw : |(5128685053/10000000000 : ℝ)|=(5128685053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46480091/250000000 : ℝ)|^4815 ≤ (11802183499599/100000000000000 : ℝ)^3791
        have hw : |(-46480091/250000000 : ℝ)|=(46480091/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s1_3 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (419143329/1000000000 : ℝ)*x 0 + (1863192521/5000000000 : ℝ)*x 1 + (146840269/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419143329/1000000000 : ℝ)^4815 ≤ (16570195004887/50000000000000 : ℝ)^3791 := by
    have hnat : (419143329 : ℕ)^4815*50000000000000^3791 ≤ 16570195004887^3791*1000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419143329 1000000000 16570195004887 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863192521/5000000000 : ℝ)^4815 ≤ (5708431352443/20000000000000 : ℝ)^3791 := by
    have hnat : (1863192521 : ℕ)^4815*20000000000000^3791 ≤ 5708431352443^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863192521 5000000000 5708431352443 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146840269/312500000 : ℝ)^4815 ≤ (38317453207607/100000000000000 : ℝ)^3791 := by
    have hnat : (146840269 : ℕ)^4815*100000000000000^3791 ≤ 38317453207607^3791*312500000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146840269 312500000 38317453207607 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419143329/1000000000 : ℝ), (1863192521/5000000000 : ℝ), (146840269/312500000 : ℝ)] ![(16570195004887/50000000000000 : ℝ), (5708431352443/20000000000000 : ℝ), (38317453207607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419143329/1000000000 : ℝ)|^4815 ≤ (16570195004887/50000000000000 : ℝ)^3791
        have hw : |(419143329/1000000000 : ℝ)|=(419143329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1863192521/5000000000 : ℝ)|^4815 ≤ (5708431352443/20000000000000 : ℝ)^3791
        have hw : |(1863192521/5000000000 : ℝ)|=(1863192521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146840269/312500000 : ℝ)|^4815 ≤ (38317453207607/100000000000000 : ℝ)^3791
        have hw : |(146840269/312500000 : ℝ)|=(146840269/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s1_4 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-828317949/5000000000 : ℝ)*x 0 + (1283201471/2500000000 : ℝ)*x 1 + (2756542331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828317949/5000000000 : ℝ)^4815 ≤ (10193652299233/100000000000000 : ℝ)^3791 := by
    have hnat : (828317949 : ℕ)^4815*100000000000000^3791 ≤ 10193652299233^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828317949 5000000000 10193652299233 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283201471/2500000000 : ℝ)^4815 ≤ (42866477119561/100000000000000 : ℝ)^3791 := by
    have hnat : (1283201471 : ℕ)^4815*100000000000000^3791 ≤ 42866477119561^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283201471 2500000000 42866477119561 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2756542331/5000000000 : ℝ)^4815 ≤ (46939870571857/100000000000000 : ℝ)^3791 := by
    have hnat : (2756542331 : ℕ)^4815*100000000000000^3791 ≤ 46939870571857^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756542331 5000000000 46939870571857 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-828317949/5000000000 : ℝ), (1283201471/2500000000 : ℝ), (2756542331/5000000000 : ℝ)] ![(10193652299233/100000000000000 : ℝ), (42866477119561/100000000000000 : ℝ), (46939870571857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-828317949/5000000000 : ℝ)|^4815 ≤ (10193652299233/100000000000000 : ℝ)^3791
        have hw : |(-828317949/5000000000 : ℝ)|=(828317949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283201471/2500000000 : ℝ)|^4815 ≤ (42866477119561/100000000000000 : ℝ)^3791
        have hw : |(1283201471/2500000000 : ℝ)|=(1283201471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2756542331/5000000000 : ℝ)|^4815 ≤ (46939870571857/100000000000000 : ℝ)^3791
        have hw : |(2756542331/5000000000 : ℝ)|=(2756542331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s1_5 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264282759/10000000000 : ℝ)*x 0 + (-737401851/5000000000 : ℝ)*x 1 + (5513085001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264282759/10000000000 : ℝ)^4815 ≤ (44265888637983/100000000000000 : ℝ)^3791 := by
    have hnat : (5264282759 : ℕ)^4815*100000000000000^3791 ≤ 44265888637983^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264282759 10000000000 44265888637983 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737401851/5000000000 : ℝ)^4815 ≤ (8794237105189/100000000000000 : ℝ)^3791 := by
    have hnat : (737401851 : ℕ)^4815*100000000000000^3791 ≤ 8794237105189^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737401851 5000000000 8794237105189 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513085001/10000000000 : ℝ)^4815 ≤ (5867484279729/12500000000000 : ℝ)^3791 := by
    have hnat : (5513085001 : ℕ)^4815*12500000000000^3791 ≤ 5867484279729^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513085001 10000000000 5867484279729 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264282759/10000000000 : ℝ), (-737401851/5000000000 : ℝ), (5513085001/10000000000 : ℝ)] ![(44265888637983/100000000000000 : ℝ), (8794237105189/100000000000000 : ℝ), (5867484279729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264282759/10000000000 : ℝ)|^4815 ≤ (44265888637983/100000000000000 : ℝ)^3791
        have hw : |(5264282759/10000000000 : ℝ)|=(5264282759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-737401851/5000000000 : ℝ)|^4815 ≤ (8794237105189/100000000000000 : ℝ)^3791
        have hw : |(-737401851/5000000000 : ℝ)|=(737401851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513085001/10000000000 : ℝ)|^4815 ≤ (5867484279729/12500000000000 : ℝ)^3791
        have hw : |(5513085001/10000000000 : ℝ)|=(5513085001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s1_6 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264282111/10000000000 : ℝ)*x 0 + (5513085243/10000000000 : ℝ)*x 1 + (-92175267/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264282111/10000000000 : ℝ)^4815 ≤ (44265881717323/100000000000000 : ℝ)^3791 := by
    have hnat : (5264282111 : ℕ)^4815*100000000000000^3791 ≤ 44265881717323^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264282111 10000000000 44265881717323 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513085243/10000000000 : ℝ)^4815 ≤ (1173496921371/2500000000000 : ℝ)^3791 := by
    have hnat : (5513085243 : ℕ)^4815*2500000000000^3791 ≤ 1173496921371^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513085243 10000000000 1173496921371 2500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92175267/625000000 : ℝ)^4815 ≤ (4397120711091/50000000000000 : ℝ)^3791 := by
    have hnat : (92175267 : ℕ)^4815*50000000000000^3791 ≤ 4397120711091^3791*625000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92175267 625000000 4397120711091 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264282111/10000000000 : ℝ), (5513085243/10000000000 : ℝ), (-92175267/625000000 : ℝ)] ![(44265881717323/100000000000000 : ℝ), (1173496921371/2500000000000 : ℝ), (4397120711091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264282111/10000000000 : ℝ)|^4815 ≤ (44265881717323/100000000000000 : ℝ)^3791
        have hw : |(5264282111/10000000000 : ℝ)|=(5264282111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513085243/10000000000 : ℝ)|^4815 ≤ (1173496921371/2500000000000 : ℝ)^3791
        have hw : |(5513085243/10000000000 : ℝ)|=(5513085243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92175267/625000000 : ℝ)|^4815 ≤ (4397120711091/50000000000000 : ℝ)^3791
        have hw : |(-92175267/625000000 : ℝ)|=(92175267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s1_7 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838384293/2000000000 : ℝ)*x 0 + (4688578217/10000000000 : ℝ)*x 1 + (467106341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838384293/2000000000 : ℝ)^4815 ≤ (2071580783503/6250000000000 : ℝ)^3791 := by
    have hnat : (838384293 : ℕ)^4815*6250000000000^3791 ≤ 2071580783503^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838384293 2000000000 2071580783503 6250000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4688578217/10000000000 : ℝ)^4815 ≤ (38210697687713/100000000000000 : ℝ)^3791 := by
    have hnat : (4688578217 : ℕ)^4815*100000000000000^3791 ≤ 38210697687713^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4688578217 10000000000 38210697687713 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467106341/1250000000 : ℝ)^4815 ≤ (28644009769429/100000000000000 : ℝ)^3791 := by
    have hnat : (467106341 : ℕ)^4815*100000000000000^3791 ≤ 28644009769429^3791*1250000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467106341 1250000000 28644009769429 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838384293/2000000000 : ℝ), (4688578217/10000000000 : ℝ), (467106341/1250000000 : ℝ)] ![(2071580783503/6250000000000 : ℝ), (38210697687713/100000000000000 : ℝ), (28644009769429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838384293/2000000000 : ℝ)|^4815 ≤ (2071580783503/6250000000000 : ℝ)^3791
        have hw : |(838384293/2000000000 : ℝ)|=(838384293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4688578217/10000000000 : ℝ)|^4815 ≤ (38210697687713/100000000000000 : ℝ)^3791
        have hw : |(4688578217/10000000000 : ℝ)|=(4688578217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467106341/1250000000 : ℝ)|^4815 ≤ (28644009769429/100000000000000 : ℝ)^3791
        have hw : |(467106341/1250000000 : ℝ)|=(467106341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1624_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5981/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (937/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4403/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5981/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5981/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5981/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5981/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5981/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5981/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4321/100000 : ℝ) ^ (4811/1024 : ℝ) ≤ (38872676013111/100000000000000000000 : ℝ) := by
    have hpowers : (4321/100000 : ℝ)^4811 ≤ (38872676013111/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4321 : ℕ)^4811*100000000000000000000^1024 ≤ 38872676013111^1024*100000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4321 100000 38872676013111 100000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4321/100000 : ℝ)) (X := (38872676013111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5981/25000 : ℝ) ^ (4811/1024 : ℝ) ≤ (120673170779226927/100000000000000000000 : ℝ) := by
    have hpowers : (5981/25000 : ℝ)^4811 ≤ (120673170779226927/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5981 : ℕ)^4811*100000000000000000000^1024 ≤ 120673170779226927^1024*25000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5981 25000 120673170779226927 100000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5981/25000 : ℝ)) (X := (120673170779226927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000038872676013111/50000000000000000000 : ℝ) ≤ (10000001654774811/10000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50000038872676013111/50000000000000000000 : ℝ)^1024 ≤ (10000001654774811/10000000000000000 : ℝ)^4811 := by
      have hnat : (50000038872676013111 : ℕ)^1024*10000000000000000^4811 ≤ 10000001654774811^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000038872676013111 50000000000000000000 10000001654774811 10000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001654774811/10000000000000000 : ℝ)) (X := (50000038872676013111/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50060356021727620019/50000000000000000000 : ℝ) ≤ (10002568082490111/10000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50060356021727620019/50000000000000000000 : ℝ)^1024 ≤ (10002568082490111/10000000000000000 : ℝ)^4811 := by
      have hnat : (50060356021727620019 : ℕ)^1024*10000000000000000^4811 ≤ 10002568082490111^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50060356021727620019 50000000000000000000 10002568082490111 10000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002568082490111/10000000000000000 : ℝ)) (X := (50060356021727620019/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50120673170779226927/50000000000000000000 : ℝ) ≤ (10005134510205411/10000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50120673170779226927/50000000000000000000 : ℝ)^1024 ≤ (10005134510205411/10000000000000000 : ℝ)^4811 := by
      have hnat : (50120673170779226927 : ℕ)^1024*10000000000000000^4811 ≤ 10005134510205411^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50120673170779226927 50000000000000000000 10005134510205411 10000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005134510205411/10000000000000000 : ℝ)) (X := (50120673170779226927/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(38872676013111/100000000000000000000 : ℝ) ≤ ((196007853370234997433/196030000000000000000 : ℝ)+2*(25664277153/19603000000000 : ℝ)*(4321/100000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (196007853370234997433/196030000000000000000 : ℝ)+2*(25664277153/19603000000000 : ℝ)*(4321/100000 : ℝ)=(10000001654774811/10000000000000000 : ℝ) by norm_num, show 1+2*(38872676013111/100000000000000000000 : ℝ)=(50000038872676013111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(120673170779226927/100000000000000000000 : ℝ)+(38872676013111/100000000000000000000 : ℝ) ≤ ((196007853370234997433/196030000000000000000 : ℝ)+(25664277153/19603000000000 : ℝ)*((5981/25000 : ℝ)+(4321/100000 : ℝ)))^(4811/1024 : ℝ) := by
    rw [show (196007853370234997433/196030000000000000000 : ℝ)+(25664277153/19603000000000 : ℝ)*((5981/25000 : ℝ)+(4321/100000 : ℝ))=(10002568082490111/10000000000000000 : ℝ) by norm_num, show 1+(120673170779226927/100000000000000000000 : ℝ)+(38872676013111/100000000000000000000 : ℝ)=(50060356021727620019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(120673170779226927/100000000000000000000 : ℝ) ≤ ((196007853370234997433/196030000000000000000 : ℝ)+2*(25664277153/19603000000000 : ℝ)*(5981/25000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (196007853370234997433/196030000000000000000 : ℝ)+2*(25664277153/19603000000000 : ℝ)*(5981/25000 : ℝ)=(10005134510205411/10000000000000000 : ℝ) by norm_num, show 1+2*(120673170779226927/100000000000000000000 : ℝ)=(50120673170779226927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (196007853370234997433/196030000000000000000 : ℝ)*(X 1 0+X 2 0)+(25664277153/19603000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (4321/100000 : ℝ)) (hi := (5981/25000 : ℝ)) (c := (196007853370234997433/196030000000000000000 : ℝ)) (alpha := (25664277153/19603000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (196007853370234997433/196030000000000000000 : ℝ)*(X 0 1+X 2 1)+(25664277153/19603000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (4321/100000 : ℝ)) (hi := (5981/25000 : ℝ)) (c := (196007853370234997433/196030000000000000000 : ℝ)) (alpha := (25664277153/19603000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (196007853370234997433/196030000000000000000 : ℝ)*(X 0 2+X 1 2)+(25664277153/19603000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (4321/100000 : ℝ)) (hi := (5981/25000 : ℝ)) (c := (196007853370234997433/196030000000000000000 : ℝ)) (alpha := (25664277153/19603000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1656439907/10000000000 : ℝ)*X 0 0+(2758633373/5000000000 : ℝ)*X 0 1+(1025737159/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214714471/400000000 : ℝ)*X 1 0+(-464800867/2500000000 : ℝ)*X 1 1+(5128685583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367862169/10000000000 : ℝ)*X 2 0+(5128685053/10000000000 : ℝ)*X 2 1+(-46480091/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419143329/1000000000 : ℝ)*X 0 0+(1863192521/5000000000 : ℝ)*X 0 1+(146840269/312500000 : ℝ)*X 0 2+(419143329/1000000000 : ℝ)*X 1 0+(1863192521/5000000000 : ℝ)*X 1 1+(146840269/312500000 : ℝ)*X 1 2+(419143329/1000000000 : ℝ)*X 2 0+(1863192521/5000000000 : ℝ)*X 2 1+(146840269/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-828317949/5000000000 : ℝ)*X 0 0+(1283201471/2500000000 : ℝ)*X 0 1+(2756542331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264282759/10000000000 : ℝ)*X 1 0+(-737401851/5000000000 : ℝ)*X 1 1+(5513085001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5264282111/10000000000 : ℝ)*X 2 0+(5513085243/10000000000 : ℝ)*X 2 1+(-92175267/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838384293/2000000000 : ℝ)*X 0 0+(4688578217/10000000000 : ℝ)*X 0 1+(467106341/1250000000 : ℝ)*X 0 2+(838384293/2000000000 : ℝ)*X 1 0+(4688578217/10000000000 : ℝ)*X 1 1+(467106341/1250000000 : ℝ)*X 1 2+(838384293/2000000000 : ℝ)*X 2 0+(4688578217/10000000000 : ℝ)*X 2 1+(467106341/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120821674477997624367/19143554687500000000000000 : ℝ) := by norm_num
    linear_combination (16727063/5000000000000 : ℝ)*(base1) + (547971339/50000000000000 : ℝ)*(base19) + (1284835113/100000000000000 : ℝ)*(base23) + (7698253/5000000000000 : ℝ)*(upper3) + (83609843/100000000000000 : ℝ)*(upper5) + (360175365135457/20000000000000 : ℝ)*(major0) + (360175365135457/20000000000000 : ℝ)*(major1) + (360175365135457/20000000000000 : ℝ)*(major2) + (2573470929050903/100000000000000 : ℝ)*(sp0) + (128673674941573/5000000000000 : ℝ)*(sp1) + (1286736654969513/50000000000000 : ℝ)*(sp2) + (205655168972563/20000000000000 : ℝ)*(sp3) + (800052899/20000000000000 : ℝ)*(sp4) + (1333399009/50000000000000 : ℝ)*(sp7) + (1028278846202093/100000000000000 : ℝ)*(f.failure) + (1286737297387069/50000000000000 : ℝ)*(f.sum) + (48336753332867/19603000000000000000000000000 : ℝ)*base66 + (4804722443209881881/3920600000000000000000000000000000 : ℝ)*base67 + (2460125838902881881/3920600000000000000000000000000000 : ℝ)*base69 + (1095200231370281881/3920600000000000000000000000000000 : ℝ)*base71 + (16199562109267/4900750000000000000000000000 : ℝ)*base74 + (20566117058260118119/3920600000000000000000000000000000 : ℝ)*base76 + (30507446472646118119/3920600000000000000000000000000000 : ℝ)*base78 + (30606600014886118119/3920600000000000000000000000000000 : ℝ)*base80 + (6835356659063/4900750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12138209/2000000000000000000000 : ℝ)*base89 + (12138209/2000000000000000000000 : ℝ)*base91 + (12138209/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50105633940966700311793319817/4900750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1999384639/100000000000000 : ℝ)*(base19) + (854835929/50000000000000 : ℝ)*(base23) + (24318511/100000000000000 : ℝ)*(upper2) + (99032769/25000000000000 : ℝ)*(upper3) + (110828381/100000000000000 : ℝ)*(upper5) + (920091471341083/50000000000000 : ℝ)*(major0) + (920091471341083/50000000000000 : ℝ)*(major1) + (920091471341083/50000000000000 : ℝ)*(major2) + (1918969891/12500000000000 : ℝ)*(sp1) + (3682689583/25000000000000 : ℝ)*(sp2) + (657410845455737/25000000000000 : ℝ)*(sp4) + (2629626030679181/100000000000000 : ℝ)*(sp5) + (1314813470696379/50000000000000 : ℝ)*(sp6) + (1050722162738893/100000000000000 : ℝ)*(sp7) + (1050722162738893/100000000000000 : ℝ)*(f.failure) + (657410845455737/25000000000000 : ℝ)*(f.sum) + (57451971528463/19603000000000000000000000000 : ℝ)*base66 + (6644357177442939939/9801500000000000000000000000000000 : ℝ)*base67 + (45447359920957560061/9801500000000000000000000000000000 : ℝ)*base70 + (8781155416873560061/9801500000000000000000000000000000 : ℝ)*base72 + (3520045327097/3920600000000000000000000000 : ℝ)*base74 + (24451490603501060061/9801500000000000000000000000000000 : ℝ)*base76 + (34182935185974060061/9801500000000000000000000000000000 : ℝ)*base78 + (1352960965405939939/9801500000000000000000000000000000 : ℝ)*base79 + (2051390826037/612593750000000000000000000 : ℝ)*base82 + (716609/2000000000000000000000 : ℝ)*base89 + (716609/2000000000000000000000 : ℝ)*base91 + (716609/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1624_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5981/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (937/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4403/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1624_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1624_s2_0 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1668534641/10000000000 : ℝ)*x 0 + (1365227057/2500000000 : ℝ)*x 1 + (1294276109/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1668534641/10000000000 : ℝ)^4815 ≤ (10286734509137/100000000000000 : ℝ)^3791 := by
    have hnat : (1668534641 : ℕ)^4815*100000000000000^3791 ≤ 10286734509137^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668534641 10000000000 10286734509137 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365227057/2500000000 : ℝ)^4815 ≤ (23188176556893/50000000000000 : ℝ)^3791 := by
    have hnat : (1365227057 : ℕ)^4815*50000000000000^3791 ≤ 23188176556893^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365227057 2500000000 23188176556893 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294276109/2500000000 : ℝ)^4815 ≤ (43336912366721/100000000000000 : ℝ)^3791 := by
    have hnat : (1294276109 : ℕ)^4815*100000000000000^3791 ≤ 43336912366721^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294276109 2500000000 43336912366721 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1668534641/10000000000 : ℝ), (1365227057/2500000000 : ℝ), (1294276109/2500000000 : ℝ)] ![(10286734509137/100000000000000 : ℝ), (23188176556893/50000000000000 : ℝ), (43336912366721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1668534641/10000000000 : ℝ)|^4815 ≤ (10286734509137/100000000000000 : ℝ)^3791
        have hw : |(-1668534641/10000000000 : ℝ)|=(1668534641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365227057/2500000000 : ℝ)|^4815 ≤ (23188176556893/50000000000000 : ℝ)^3791
        have hw : |(1365227057/2500000000 : ℝ)|=(1365227057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294276109/2500000000 : ℝ)|^4815 ≤ (43336912366721/100000000000000 : ℝ)^3791
        have hw : |(1294276109/2500000000 : ℝ)|=(1294276109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s2_1 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070617751/2000000000 : ℝ)*x 0 + (-362991491/2000000000 : ℝ)*x 1 + (2588552261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070617751/2000000000 : ℝ)^4815 ≤ (11304122865043/25000000000000 : ℝ)^3791 := by
    have hnat : (1070617751 : ℕ)^4815*25000000000000^3791 ≤ 11304122865043^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070617751 2000000000 11304122865043 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (362991491/2000000000 : ℝ)^4815 ≤ (11446595239179/100000000000000 : ℝ)^3791 := by
    have hnat : (362991491 : ℕ)^4815*100000000000000^3791 ≤ 11446595239179^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362991491 2000000000 11446595239179 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588552261/5000000000 : ℝ)^4815 ≤ (4333691328107/10000000000000 : ℝ)^3791 := by
    have hnat : (2588552261 : ℕ)^4815*10000000000000^3791 ≤ 4333691328107^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588552261 5000000000 4333691328107 10000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070617751/2000000000 : ℝ), (-362991491/2000000000 : ℝ), (2588552261/5000000000 : ℝ)] ![(11304122865043/25000000000000 : ℝ), (11446595239179/100000000000000 : ℝ), (4333691328107/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070617751/2000000000 : ℝ)|^4815 ≤ (11304122865043/25000000000000 : ℝ)^3791
        have hw : |(1070617751/2000000000 : ℝ)|=(1070617751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-362991491/2000000000 : ℝ)|^4815 ≤ (11446595239179/100000000000000 : ℝ)^3791
        have hw : |(-362991491/2000000000 : ℝ)|=(362991491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588552261/5000000000 : ℝ)|^4815 ≤ (4333691328107/10000000000000 : ℝ)^3791
        have hw : |(2588552261/5000000000 : ℝ)|=(2588552261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s2_2 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676544397/5000000000 : ℝ)*x 0 + (5177104391/10000000000 : ℝ)*x 1 + (-1814957577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676544397/5000000000 : ℝ)^4815 ≤ (2260824593929/5000000000000 : ℝ)^3791 := by
    have hnat : (2676544397 : ℕ)^4815*5000000000000^3791 ≤ 2260824593929^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676544397 5000000000 2260824593929 5000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177104391/10000000000 : ℝ)^4815 ≤ (21668455944141/50000000000000 : ℝ)^3791 := by
    have hnat : (5177104391 : ℕ)^4815*50000000000000^3791 ≤ 21668455944141^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177104391 10000000000 21668455944141 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1814957577/10000000000 : ℝ)^4815 ≤ (11446596216443/100000000000000 : ℝ)^3791 := by
    have hnat : (1814957577 : ℕ)^4815*100000000000000^3791 ≤ 11446596216443^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814957577 10000000000 11446596216443 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676544397/5000000000 : ℝ), (5177104391/10000000000 : ℝ), (-1814957577/10000000000 : ℝ)] ![(2260824593929/5000000000000 : ℝ), (21668455944141/50000000000000 : ℝ), (11446596216443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676544397/5000000000 : ℝ)|^4815 ≤ (2260824593929/5000000000000 : ℝ)^3791
        have hw : |(2676544397/5000000000 : ℝ)|=(2676544397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177104391/10000000000 : ℝ)|^4815 ≤ (21668455944141/50000000000000 : ℝ)^3791
        have hw : |(5177104391/10000000000 : ℝ)|=(5177104391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1814957577/10000000000 : ℝ)|^4815 ≤ (11446596216443/100000000000000 : ℝ)^3791
        have hw : |(-1814957577/10000000000 : ℝ)|=(1814957577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s2_3 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4200391579/10000000000 : ℝ)*x 0 + (1928284113/5000000000 : ℝ)*x 1 + (913368847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200391579/10000000000 : ℝ)^4815 ≤ (2076898668489/6250000000000 : ℝ)^3791 := by
    have hnat : (4200391579 : ℕ)^4815*6250000000000^3791 ≤ 2076898668489^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200391579 10000000000 2076898668489 6250000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928284113/5000000000 : ℝ)^4815 ≤ (1490727840877/5000000000000 : ℝ)^3791 := by
    have hnat : (1928284113 : ℕ)^4815*5000000000000^3791 ≤ 1490727840877^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928284113 5000000000 1490727840877 5000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (913368847/2000000000 : ℝ)^4815 ≤ (36955064465733/100000000000000 : ℝ)^3791 := by
    have hnat : (913368847 : ℕ)^4815*100000000000000^3791 ≤ 36955064465733^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913368847 2000000000 36955064465733 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200391579/10000000000 : ℝ), (1928284113/5000000000 : ℝ), (913368847/2000000000 : ℝ)] ![(2076898668489/6250000000000 : ℝ), (1490727840877/5000000000000 : ℝ), (36955064465733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200391579/10000000000 : ℝ)|^4815 ≤ (2076898668489/6250000000000 : ℝ)^3791
        have hw : |(4200391579/10000000000 : ℝ)|=(4200391579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1928284113/5000000000 : ℝ)|^4815 ≤ (1490727840877/5000000000000 : ℝ)^3791
        have hw : |(1928284113/5000000000 : ℝ)|=(1928284113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(913368847/2000000000 : ℝ)|^4815 ≤ (36955064465733/100000000000000 : ℝ)^3791
        have hw : |(913368847/2000000000 : ℝ)|=(913368847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s2_4 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-333722173/2000000000 : ℝ)*x 0 + (5179308969/10000000000 : ℝ)*x 1 + (5458679663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333722173/2000000000 : ℝ)^4815 ≤ (2057466275683/20000000000000 : ℝ)^3791 := by
    have hnat : (333722173 : ℕ)^4815*20000000000000^3791 ≤ 2057466275683^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333722173 2000000000 2057466275683 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179308969/10000000000 : ℝ)^4815 ≤ (43360352232703/100000000000000 : ℝ)^3791 := by
    have hnat : (5179308969 : ℕ)^4815*100000000000000^3791 ≤ 43360352232703^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179308969 10000000000 43360352232703 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458679663/10000000000 : ℝ)^4815 ≤ (46352316372503/100000000000000 : ℝ)^3791 := by
    have hnat : (5458679663 : ℕ)^4815*100000000000000^3791 ≤ 46352316372503^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458679663 10000000000 46352316372503 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-333722173/2000000000 : ℝ), (5179308969/10000000000 : ℝ), (5458679663/10000000000 : ℝ)] ![(2057466275683/20000000000000 : ℝ), (43360352232703/100000000000000 : ℝ), (46352316372503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-333722173/2000000000 : ℝ)|^4815 ≤ (2057466275683/20000000000000 : ℝ)^3791
        have hw : |(-333722173/2000000000 : ℝ)|=(333722173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179308969/10000000000 : ℝ)|^4815 ≤ (43360352232703/100000000000000 : ℝ)^3791
        have hw : |(5179308969/10000000000 : ℝ)|=(5179308969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458679663/10000000000 : ℝ)|^4815 ≤ (46352316372503/100000000000000 : ℝ)^3791
        have hw : |(5458679663/10000000000 : ℝ)|=(5458679663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s2_5 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277531569/10000000000 : ℝ)*x 0 + (-1533382103/10000000000 : ℝ)*x 1 + (2729339889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277531569/10000000000 : ℝ)^4815 ≤ (1776297375859/4000000000000 : ℝ)^3791 := by
    have hnat : (5277531569 : ℕ)^4815*4000000000000^3791 ≤ 1776297375859^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277531569 10000000000 1776297375859 4000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1533382103/10000000000 : ℝ)^4815 ≤ (9240247979759/100000000000000 : ℝ)^3791 := by
    have hnat : (1533382103 : ℕ)^4815*100000000000000^3791 ≤ 9240247979759^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533382103 10000000000 9240247979759 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729339889/5000000000 : ℝ)^4815 ≤ (9270463522559/20000000000000 : ℝ)^3791 := by
    have hnat : (2729339889 : ℕ)^4815*20000000000000^3791 ≤ 9270463522559^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729339889 5000000000 9270463522559 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277531569/10000000000 : ℝ), (-1533382103/10000000000 : ℝ), (2729339889/5000000000 : ℝ)] ![(1776297375859/4000000000000 : ℝ), (9240247979759/100000000000000 : ℝ), (9270463522559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277531569/10000000000 : ℝ)|^4815 ≤ (1776297375859/4000000000000 : ℝ)^3791
        have hw : |(5277531569/10000000000 : ℝ)|=(5277531569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1533382103/10000000000 : ℝ)|^4815 ≤ (9240247979759/100000000000000 : ℝ)^3791
        have hw : |(-1533382103/10000000000 : ℝ)|=(1533382103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729339889/5000000000 : ℝ)|^4815 ≤ (9270463522559/20000000000000 : ℝ)^3791
        have hw : |(2729339889/5000000000 : ℝ)|=(2729339889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s2_6 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277531821/10000000000 : ℝ)*x 0 + (1364669803/2500000000 : ℝ)*x 1 + (-1533382549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277531821/10000000000 : ℝ)^4815 ≤ (44407437089671/100000000000000 : ℝ)^3791 := by
    have hnat : (5277531821 : ℕ)^4815*100000000000000^3791 ≤ 44407437089671^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277531821 10000000000 44407437089671 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364669803/2500000000 : ℝ)^4815 ≤ (23176155754199/50000000000000 : ℝ)^3791 := by
    have hnat : (1364669803 : ℕ)^4815*50000000000000^3791 ≤ 23176155754199^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364669803 2500000000 23176155754199 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1533382549/10000000000 : ℝ)^4815 ≤ (9240251393343/100000000000000 : ℝ)^3791 := by
    have hnat : (1533382549 : ℕ)^4815*100000000000000^3791 ≤ 9240251393343^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533382549 10000000000 9240251393343 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277531821/10000000000 : ℝ), (1364669803/2500000000 : ℝ), (-1533382549/10000000000 : ℝ)] ![(44407437089671/100000000000000 : ℝ), (23176155754199/50000000000000 : ℝ), (9240251393343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277531821/10000000000 : ℝ)|^4815 ≤ (44407437089671/100000000000000 : ℝ)^3791
        have hw : |(5277531821/10000000000 : ℝ)|=(5277531821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364669803/2500000000 : ℝ)|^4815 ≤ (23176155754199/50000000000000 : ℝ)^3791
        have hw : |(1364669803/2500000000 : ℝ)|=(1364669803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1533382549/10000000000 : ℝ)|^4815 ≤ (9240251393343/100000000000000 : ℝ)^3791
        have hw : |(-1533382549/10000000000 : ℝ)|=(1533382549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s2_7 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050145669/2500000000 : ℝ)*x 0 + (2280663547/5000000000 : ℝ)*x 1 + (1931072769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050145669/2500000000 : ℝ)^4815 ≤ (16616149443691/50000000000000 : ℝ)^3791 := by
    have hnat : (1050145669 : ℕ)^4815*50000000000000^3791 ≤ 16616149443691^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050145669 2500000000 16616149443691 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2280663547/5000000000 : ℝ)^4815 ≤ (36898369634181/100000000000000 : ℝ)^3791 := by
    have hnat : (2280663547 : ℕ)^4815*100000000000000^3791 ≤ 36898369634181^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280663547 5000000000 36898369634181 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931072769/5000000000 : ℝ)^4815 ≤ (29869331462767/100000000000000 : ℝ)^3791 := by
    have hnat : (1931072769 : ℕ)^4815*100000000000000^3791 ≤ 29869331462767^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931072769 5000000000 29869331462767 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050145669/2500000000 : ℝ), (2280663547/5000000000 : ℝ), (1931072769/5000000000 : ℝ)] ![(16616149443691/50000000000000 : ℝ), (36898369634181/100000000000000 : ℝ), (29869331462767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050145669/2500000000 : ℝ)|^4815 ≤ (16616149443691/50000000000000 : ℝ)^3791
        have hw : |(1050145669/2500000000 : ℝ)|=(1050145669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2280663547/5000000000 : ℝ)|^4815 ≤ (36898369634181/100000000000000 : ℝ)^3791
        have hw : |(2280663547/5000000000 : ℝ)|=(2280663547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1931072769/5000000000 : ℝ)|^4815 ≤ (29869331462767/100000000000000 : ℝ)^3791
        have hw : |(1931072769/5000000000 : ℝ)|=(1931072769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1624_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4403/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (937/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2083/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16437/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4403/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (937/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4403/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (937/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4403/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (937/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4403/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (937/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4403/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (937/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4403/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (937/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (937/10000 : ℝ) ^ (4811/1024 : ℝ) ≤ (295130138635267/20000000000000000000 : ℝ) := by
    have hpowers : (937/10000 : ℝ)^4811 ≤ (295130138635267/20000000000000000000 : ℝ)^1024 := by
      have hnat : (937 : ℕ)^4811*20000000000000000000^1024 ≤ 295130138635267^1024*10000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        937 10000 295130138635267 20000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (937/10000 : ℝ)) (X := (295130138635267/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4403/25000 : ℝ) ^ (4811/1024 : ℝ) ≤ (28617158429106579/100000000000000000000 : ℝ) := by
    have hpowers : (4403/25000 : ℝ)^4811 ≤ (28617158429106579/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4403 : ℕ)^4811*100000000000000000000^1024 ≤ 28617158429106579^1024*25000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4403 25000 28617158429106579 100000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4403/25000 : ℝ)) (X := (28617158429106579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000295130138635267/10000000000000000000 : ℝ) ≤ (10000062816410647/10000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (10000295130138635267/10000000000000000000 : ℝ)^1024 ≤ (10000062816410647/10000000000000000 : ℝ)^4811 := by
      have hnat : (10000295130138635267 : ℕ)^1024*10000000000000000^4811 ≤ 10000062816410647^4811*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000295130138635267 10000000000000000000 10000062816410647 10000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062816410647/10000000000000000 : ℝ)) (X := (10000295130138635267/10000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015046404561141457/50000000000000000000 : ℝ) ≤ (2000128087248017/2000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50015046404561141457/50000000000000000000 : ℝ)^1024 ≤ (2000128087248017/2000000000000000 : ℝ)^4811 := by
      have hnat : (50015046404561141457 : ℕ)^1024*2000000000000000^4811 ≤ 2000128087248017^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015046404561141457 50000000000000000000 2000128087248017 2000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000128087248017/2000000000000000 : ℝ)) (X := (50015046404561141457/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028617158429106579/50000000000000000000 : ℝ) ≤ (10001218056069523/10000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50028617158429106579/50000000000000000000 : ℝ)^1024 ≤ (10001218056069523/10000000000000000 : ℝ)^4811 := by
      have hnat : (50028617158429106579 : ℕ)^1024*10000000000000000^4811 ≤ 10001218056069523^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028617158429106579 50000000000000000000 10001218056069523 10000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001218056069523/10000000000000000 : ℝ)) (X := (50028617158429106579/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(295130138635267/20000000000000000000 : ℝ) ≤ ((41204846568626442227/41210000000000000000 : ℝ)+2*(288809914719/412100000000000 : ℝ)*(937/10000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (41204846568626442227/41210000000000000000 : ℝ)+2*(288809914719/412100000000000 : ℝ)*(937/10000 : ℝ)=(10000062816410647/10000000000000000 : ℝ) by norm_num, show 1+2*(295130138635267/20000000000000000000 : ℝ)=(10000295130138635267/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28617158429106579/100000000000000000000 : ℝ)+(295130138635267/20000000000000000000 : ℝ) ≤ ((41204846568626442227/41210000000000000000 : ℝ)+(288809914719/412100000000000 : ℝ)*((4403/25000 : ℝ)+(937/10000 : ℝ)))^(4811/1024 : ℝ) := by
    rw [show (41204846568626442227/41210000000000000000 : ℝ)+(288809914719/412100000000000 : ℝ)*((4403/25000 : ℝ)+(937/10000 : ℝ))=(2000128087248017/2000000000000000 : ℝ) by norm_num, show 1+(28617158429106579/100000000000000000000 : ℝ)+(295130138635267/20000000000000000000 : ℝ)=(50015046404561141457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28617158429106579/100000000000000000000 : ℝ) ≤ ((41204846568626442227/41210000000000000000 : ℝ)+2*(288809914719/412100000000000 : ℝ)*(4403/25000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (41204846568626442227/41210000000000000000 : ℝ)+2*(288809914719/412100000000000 : ℝ)*(4403/25000 : ℝ)=(10001218056069523/10000000000000000 : ℝ) by norm_num, show 1+2*(28617158429106579/100000000000000000000 : ℝ)=(50028617158429106579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41204846568626442227/41210000000000000000 : ℝ)*(X 1 0+X 2 0)+(288809914719/412100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (937/10000 : ℝ)) (hi := (4403/25000 : ℝ)) (c := (41204846568626442227/41210000000000000000 : ℝ)) (alpha := (288809914719/412100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41204846568626442227/41210000000000000000 : ℝ)*(X 0 1+X 2 1)+(288809914719/412100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (937/10000 : ℝ)) (hi := (4403/25000 : ℝ)) (c := (41204846568626442227/41210000000000000000 : ℝ)) (alpha := (288809914719/412100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41204846568626442227/41210000000000000000 : ℝ)*(X 0 2+X 1 2)+(288809914719/412100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (937/10000 : ℝ)) (hi := (4403/25000 : ℝ)) (c := (41204846568626442227/41210000000000000000 : ℝ)) (alpha := (288809914719/412100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1668534641/10000000000 : ℝ)*X 0 0+(1365227057/2500000000 : ℝ)*X 0 1+(1294276109/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070617751/2000000000 : ℝ)*X 1 0+(-362991491/2000000000 : ℝ)*X 1 1+(2588552261/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676544397/5000000000 : ℝ)*X 2 0+(5177104391/10000000000 : ℝ)*X 2 1+(-1814957577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200391579/10000000000 : ℝ)*X 0 0+(1928284113/5000000000 : ℝ)*X 0 1+(913368847/2000000000 : ℝ)*X 0 2+(4200391579/10000000000 : ℝ)*X 1 0+(1928284113/5000000000 : ℝ)*X 1 1+(913368847/2000000000 : ℝ)*X 1 2+(4200391579/10000000000 : ℝ)*X 2 0+(1928284113/5000000000 : ℝ)*X 2 1+(913368847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-333722173/2000000000 : ℝ)*X 0 0+(5179308969/10000000000 : ℝ)*X 0 1+(5458679663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277531569/10000000000 : ℝ)*X 1 0+(-1533382103/10000000000 : ℝ)*X 1 1+(2729339889/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277531821/10000000000 : ℝ)*X 2 0+(1364669803/2500000000 : ℝ)*X 2 1+(-1533382549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050145669/2500000000 : ℝ)*X 0 0+(2280663547/5000000000 : ℝ)*X 0 1+(1931072769/5000000000 : ℝ)*X 0 2+(1050145669/2500000000 : ℝ)*X 1 0+(2280663547/5000000000 : ℝ)*X 1 1+(1931072769/5000000000 : ℝ)*X 1 2+(1050145669/2500000000 : ℝ)*X 2 0+(2280663547/5000000000 : ℝ)*X 2 1+(1931072769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13015223033982815117658540969/1030250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (502916673/25000000000000 : ℝ)*(base19) + (957848373/50000000000000 : ℝ)*(base23) + (65115633/100000000000000 : ℝ)*(lower2) + (71192327/20000000000000 : ℝ)*(upper3) + (177841793/100000000000000 : ℝ)*(upper5) + (1232883163325649/50000000000000 : ℝ)*(major0) + (1232883163325649/50000000000000 : ℝ)*(major1) + (1232883163325649/50000000000000 : ℝ)*(major2) + (35235866466563/1000000000000 : ℝ)*(sp0) + (880901881438571/25000000000000 : ℝ)*(sp1) + (352360762172423/10000000000000 : ℝ)*(sp2) + (8799450816237/625000000000 : ℝ)*(sp3) + (5722691169/25000000000000 : ℝ)*(sp4) + (10564181277/100000000000000 : ℝ)*(sp7) + (1407922694779197/100000000000000 : ℝ)*(f.failure) + (220225596088811/6250000000000 : ℝ)*(f.sum) + (22875152509699/10302500000000000000000000000 : ℝ)*base66 + (4053638341272119677/2060500000000000000000000000000000 : ℝ)*base68 + (11380549298898119677/2060500000000000000000000000000000 : ℝ)*base70 + (1483697949252880323/2060500000000000000000000000000000 : ℝ)*base71 + (28577545939057/5151250000000000000000000000 : ℝ)*base74 + (16449258265128119677/2060500000000000000000000000000000 : ℝ)*base76 + (10874773483847119677/2060500000000000000000000000000000 : ℝ)*base78 + (1940606538324880323/2060500000000000000000000000000000 : ℝ)*base79 + (10622519318459/10302500000000000000000000000 : ℝ)*base82 + (5448561/2000000000000000000000 : ℝ)*base89 + (5448561/2000000000000000000000 : ℝ)*base91 + (5448561/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (352494983007141956955753261/128781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85132671/20000000000000 : ℝ)*(base19) + (25994399/4000000000000 : ℝ)*(base23) + (60447529/100000000000000 : ℝ)*(upper3) + (57322809/100000000000000 : ℝ)*(lower4) + (43761601/100000000000000 : ℝ)*(upper5) + (313107275116681/12500000000000 : ℝ)*(major0) + (313107275116681/12500000000000 : ℝ)*(major1) + (313107275116681/12500000000000 : ℝ)*(major2) + (6180364291/100000000000000 : ℝ)*(sp1) + (2315082837/100000000000000 : ℝ)*(sp2) + (35794726293109/1000000000000 : ℝ)*(sp4) + (1789733011641627/50000000000000 : ℝ)*(sp5) + (447433708046011/12500000000000 : ℝ)*(sp6) + (1430243681317301/100000000000000 : ℝ)*(sp7) + (1430243681317301/100000000000000 : ℝ)*(f.failure) + (35794726293109/1000000000000 : ℝ)*(f.sum) + (12235607746329/2575625000000000000000000000 : ℝ)*base65 + (1005664056239861413/515125000000000000000000000000000 : ℝ)*base68 + (1344855449930361413/515125000000000000000000000000000 : ℝ)*base70 + (2001401150651013587/515125000000000000000000000000000 : ℝ)*base71 + (2586390408723/20605000000000000000000000000 : ℝ)*base74 + (4839996508492111413/515125000000000000000000000000000 : ℝ)*base76 + (1209714808723361413/515125000000000000000000000000000 : ℝ)*base78 + (2748724365312736413/515125000000000000000000000000000 : ℝ)*base80 + (12681091421527/20605000000000000000000000000 : ℝ)*base81 + (748087/2000000000000000000000 : ℝ)*base90 + (748087/2000000000000000000000 : ℝ)*base92 + (748087/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1624_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4403/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (937/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16437/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1624_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1624_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16437/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1624_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1624_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1624_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16437/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1624_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
