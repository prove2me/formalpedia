-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1628_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:15.88386+00:00
-- url     : https://prove2.me/submissions/821469a4-e5f8-4eaa-8b87-6b6357f942c4

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
theorem support_rectangle_w1628_box_0 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1393864811/10000000000 : ℝ)*x 0 + (1353383307/2500000000 : ℝ)*x 1 + (5413533253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1393864811/10000000000 : ℝ)^4831 ≤ (4102085160011/50000000000000 : ℝ)^3807 := by
    have hnat : (1393864811 : ℕ)^4831*50000000000000^3807 ≤ 4102085160011^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393864811 10000000000 4102085160011 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353383307/2500000000 : ℝ)^4831 ≤ (45897914697137/100000000000000 : ℝ)^3807 := by
    have hnat : (1353383307 : ℕ)^4831*100000000000000^3807 ≤ 45897914697137^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353383307 2500000000 45897914697137 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413533253/10000000000 : ℝ)^4831 ≤ (11474478741527/25000000000000 : ℝ)^3807 := by
    have hnat : (5413533253 : ℕ)^4831*25000000000000^3807 ≤ 11474478741527^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413533253 10000000000 11474478741527 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1393864811/10000000000 : ℝ), (1353383307/2500000000 : ℝ), (5413533253/10000000000 : ℝ)] ![(4102085160011/50000000000000 : ℝ), (45897914697137/100000000000000 : ℝ), (11474478741527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1393864811/10000000000 : ℝ)|^4831 ≤ (4102085160011/50000000000000 : ℝ)^3807
        have hw : |(-1393864811/10000000000 : ℝ)|=(1393864811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353383307/2500000000 : ℝ)|^4831 ≤ (45897914697137/100000000000000 : ℝ)^3807
        have hw : |(1353383307/2500000000 : ℝ)|=(1353383307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413533253/10000000000 : ℝ)|^4831 ≤ (11474478741527/25000000000000 : ℝ)^3807
        have hw : |(5413533253/10000000000 : ℝ)|=(5413533253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_1 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164101663/312500000 : ℝ)*x 0 + (-405460877/2500000000 : ℝ)*x 1 + (1353383347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164101663/312500000 : ℝ)^4831 ≤ (44159057516991/100000000000000 : ℝ)^3807 := by
    have hnat : (164101663 : ℕ)^4831*100000000000000^3807 ≤ 44159057516991^3807*312500000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164101663 312500000 44159057516991 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405460877/2500000000 : ℝ)^4831 ≤ (1242878254857/12500000000000 : ℝ)^3807 := by
    have hnat : (405460877 : ℕ)^4831*12500000000000^3807 ≤ 1242878254857^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405460877 2500000000 1242878254857 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353383347/2500000000 : ℝ)^4831 ≤ (22948958209277/50000000000000 : ℝ)^3807 := by
    have hnat : (1353383347 : ℕ)^4831*50000000000000^3807 ≤ 22948958209277^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353383347 2500000000 22948958209277 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164101663/312500000 : ℝ), (-405460877/2500000000 : ℝ), (1353383347/2500000000 : ℝ)] ![(44159057516991/100000000000000 : ℝ), (1242878254857/12500000000000 : ℝ), (22948958209277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164101663/312500000 : ℝ)|^4831 ≤ (44159057516991/100000000000000 : ℝ)^3807
        have hw : |(164101663/312500000 : ℝ)|=(164101663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405460877/2500000000 : ℝ)|^4831 ≤ (1242878254857/12500000000000 : ℝ)^3807
        have hw : |(-405460877/2500000000 : ℝ)|=(405460877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353383347/2500000000 : ℝ)|^4831 ≤ (22948958209277/50000000000000 : ℝ)^3807
        have hw : |(1353383347/2500000000 : ℝ)|=(1353383347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_2 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251253217/10000000000 : ℝ)*x 0 + (5413533393/10000000000 : ℝ)*x 1 + (-1621843501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251253217/10000000000 : ℝ)^4831 ≤ (22079528763831/50000000000000 : ℝ)^3807 := by
    have hnat : (5251253217 : ℕ)^4831*50000000000000^3807 ≤ 22079528763831^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251253217 10000000000 22079528763831 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413533393/10000000000 : ℝ)^4831 ≤ (45897916472349/100000000000000 : ℝ)^3807 := by
    have hnat : (5413533393 : ℕ)^4831*100000000000000^3807 ≤ 45897916472349^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413533393 10000000000 45897916472349 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1621843501/10000000000 : ℝ)^4831 ≤ (4971512992199/50000000000000 : ℝ)^3807 := by
    have hnat : (1621843501 : ℕ)^4831*50000000000000^3807 ≤ 4971512992199^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621843501 10000000000 4971512992199 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251253217/10000000000 : ℝ), (5413533393/10000000000 : ℝ), (-1621843501/10000000000 : ℝ)] ![(22079528763831/50000000000000 : ℝ), (45897916472349/100000000000000 : ℝ), (4971512992199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251253217/10000000000 : ℝ)|^4831 ≤ (22079528763831/50000000000000 : ℝ)^3807
        have hw : |(5251253217/10000000000 : ℝ)|=(5251253217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413533393/10000000000 : ℝ)|^4831 ≤ (45897916472349/100000000000000 : ℝ)^3807
        have hw : |(5413533393/10000000000 : ℝ)|=(5413533393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1621843501/10000000000 : ℝ)|^4831 ≤ (4971512992199/50000000000000 : ℝ)^3807
        have hw : |(-1621843501/10000000000 : ℝ)|=(1621843501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_3 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2238165863/5000000000 : ℝ)*x 0 + (254447733/625000000 : ℝ)*x 1 + (814232747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238165863/5000000000 : ℝ)^4831 ≤ (7212037200419/20000000000000 : ℝ)^3807 := by
    have hnat : (2238165863 : ℕ)^4831*20000000000000^3807 ≤ 7212037200419^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238165863 5000000000 7212037200419 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254447733/625000000 : ℝ)^4831 ≤ (31969906959743/100000000000000 : ℝ)^3807 := by
    have hnat : (254447733 : ℕ)^4831*100000000000000^3807 ≤ 31969906959743^3807*625000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254447733 625000000 31969906959743 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814232747/2000000000 : ℝ)^4831 ≤ (15984953514749/50000000000000 : ℝ)^3807 := by
    have hnat : (814232747 : ℕ)^4831*50000000000000^3807 ≤ 15984953514749^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814232747 2000000000 15984953514749 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238165863/5000000000 : ℝ), (254447733/625000000 : ℝ), (814232747/2000000000 : ℝ)] ![(7212037200419/20000000000000 : ℝ), (31969906959743/100000000000000 : ℝ), (15984953514749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238165863/5000000000 : ℝ)|^4831 ≤ (7212037200419/20000000000000 : ℝ)^3807
        have hw : |(2238165863/5000000000 : ℝ)|=(2238165863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254447733/625000000 : ℝ)|^4831 ≤ (31969906959743/100000000000000 : ℝ)^3807
        have hw : |(254447733/625000000 : ℝ)|=(254447733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(814232747/2000000000 : ℝ)|^4831 ≤ (15984953514749/50000000000000 : ℝ)^3807
        have hw : |(814232747/2000000000 : ℝ)|=(814232747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_4 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936848887/10000000000 : ℝ)*x 0 + (5214999893/10000000000 : ℝ)*x 1 + (2607499959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936848887/10000000000 : ℝ)^4831 ≤ (12454893970231/100000000000000 : ℝ)^3807 := by
    have hnat : (1936848887 : ℕ)^4831*100000000000000^3807 ≤ 12454893970231^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936848887 10000000000 12454893970231 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214999893/10000000000 : ℝ)^4831 ≤ (1367892277329/3125000000000 : ℝ)^3807 := by
    have hnat : (5214999893 : ℕ)^4831*3125000000000^3807 ≤ 1367892277329^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214999893 10000000000 1367892277329 3125000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607499959/5000000000 : ℝ)^4831 ≤ (4377255314081/10000000000000 : ℝ)^3807 := by
    have hnat : (2607499959 : ℕ)^4831*10000000000000^3807 ≤ 4377255314081^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607499959 5000000000 4377255314081 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936848887/10000000000 : ℝ), (5214999893/10000000000 : ℝ), (2607499959/5000000000 : ℝ)] ![(12454893970231/100000000000000 : ℝ), (1367892277329/3125000000000 : ℝ), (4377255314081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936848887/10000000000 : ℝ)|^4831 ≤ (12454893970231/100000000000000 : ℝ)^3807
        have hw : |(-1936848887/10000000000 : ℝ)|=(1936848887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214999893/10000000000 : ℝ)|^4831 ≤ (1367892277329/3125000000000 : ℝ)^3807
        have hw : |(5214999893/10000000000 : ℝ)|=(5214999893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607499959/5000000000 : ℝ)|^4831 ≤ (4377255314081/10000000000000 : ℝ)^3807
        have hw : |(2607499959/5000000000 : ℝ)|=(2607499959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_5 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673491421/1250000000 : ℝ)*x 0 + (-21329043/125000000 : ℝ)*x 1 + (2607499989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673491421/1250000000 : ℝ)^4831 ≤ (4562264323149/10000000000000 : ℝ)^3807 := by
    have hnat : (673491421 : ℕ)^4831*10000000000000^3807 ≤ 4562264323149^3807*1250000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673491421 1250000000 4562264323149 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21329043/125000000 : ℝ)^4831 ≤ (10604802976771/100000000000000 : ℝ)^3807 := by
    have hnat : (21329043 : ℕ)^4831*100000000000000^3807 ≤ 10604802976771^3807*125000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21329043 125000000 10604802976771 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607499989/5000000000 : ℝ)^4831 ≤ (21886276889943/50000000000000 : ℝ)^3807 := by
    have hnat : (2607499989 : ℕ)^4831*50000000000000^3807 ≤ 21886276889943^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607499989 5000000000 21886276889943 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673491421/1250000000 : ℝ), (-21329043/125000000 : ℝ), (2607499989/5000000000 : ℝ)] ![(4562264323149/10000000000000 : ℝ), (10604802976771/100000000000000 : ℝ), (21886276889943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673491421/1250000000 : ℝ)|^4831 ≤ (4562264323149/10000000000000 : ℝ)^3807
        have hw : |(673491421/1250000000 : ℝ)|=(673491421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21329043/125000000 : ℝ)|^4831 ≤ (10604802976771/100000000000000 : ℝ)^3807
        have hw : |(-21329043/125000000 : ℝ)|=(21329043/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607499989/5000000000 : ℝ)|^4831 ≤ (21886276889943/50000000000000 : ℝ)^3807
        have hw : |(2607499989/5000000000 : ℝ)|=(2607499989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_6 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077586277/2000000000 : ℝ)*x 0 + (162968749/312500000 : ℝ)*x 1 + (-170632343/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077586277/2000000000 : ℝ)^4831 ≤ (45622643414157/100000000000000 : ℝ)^3807 := by
    have hnat : (1077586277 : ℕ)^4831*100000000000000^3807 ≤ 45622643414157^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077586277 2000000000 45622643414157 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162968749/312500000 : ℝ)^4831 ≤ (21886276836687/50000000000000 : ℝ)^3807 := by
    have hnat : (162968749 : ℕ)^4831*50000000000000^3807 ≤ 21886276836687^3807*312500000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162968749 312500000 21886276836687 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170632343/1000000000 : ℝ)^4831 ≤ (662800181119/6250000000000 : ℝ)^3807 := by
    have hnat : (170632343 : ℕ)^4831*6250000000000^3807 ≤ 662800181119^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170632343 1000000000 662800181119 6250000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077586277/2000000000 : ℝ), (162968749/312500000 : ℝ), (-170632343/1000000000 : ℝ)] ![(45622643414157/100000000000000 : ℝ), (21886276836687/50000000000000 : ℝ), (662800181119/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077586277/2000000000 : ℝ)|^4831 ≤ (45622643414157/100000000000000 : ℝ)^3807
        have hw : |(1077586277/2000000000 : ℝ)|=(1077586277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162968749/312500000 : ℝ)|^4831 ≤ (21886276836687/50000000000000 : ℝ)^3807
        have hw : |(162968749/312500000 : ℝ)|=(162968749/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170632343/1000000000 : ℝ)|^4831 ≤ (662800181119/6250000000000 : ℝ)^3807
        have hw : |(-170632343/1000000000 : ℝ)|=(170632343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_7 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3913412609/10000000000 : ℝ)*x 0 + (4352288599/10000000000 : ℝ)*x 1 + (870457733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3913412609/10000000000 : ℝ)^4831 ≤ (7601547241593/25000000000000 : ℝ)^3807 := by
    have hnat : (3913412609 : ℕ)^4831*25000000000000^3807 ≤ 7601547241593^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3913412609 10000000000 7601547241593 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4352288599/10000000000 : ℝ)^4831 ≤ (4349613146941/12500000000000 : ℝ)^3807 := by
    have hnat : (4352288599 : ℕ)^4831*12500000000000^3807 ≤ 4349613146941^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352288599 10000000000 4349613146941 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870457733/2000000000 : ℝ)^4831 ≤ (2174806615321/6250000000000 : ℝ)^3807 := by
    have hnat : (870457733 : ℕ)^4831*6250000000000^3807 ≤ 2174806615321^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870457733 2000000000 2174806615321 6250000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3913412609/10000000000 : ℝ), (4352288599/10000000000 : ℝ), (870457733/2000000000 : ℝ)] ![(7601547241593/25000000000000 : ℝ), (4349613146941/12500000000000 : ℝ), (2174806615321/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3913412609/10000000000 : ℝ)|^4831 ≤ (7601547241593/25000000000000 : ℝ)^3807
        have hw : |(3913412609/10000000000 : ℝ)|=(3913412609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4352288599/10000000000 : ℝ)|^4831 ≤ (4349613146941/12500000000000 : ℝ)^3807
        have hw : |(4352288599/10000000000 : ℝ)|=(4352288599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(870457733/2000000000 : ℝ)|^4831 ≤ (2174806615321/6250000000000 : ℝ)^3807
        have hw : |(870457733/2000000000 : ℝ)|=(870457733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_8 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1821221099/10000000000 : ℝ)*x 0 + (1268187163/2500000000 : ℝ)*x 1 + (2721629547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821221099/10000000000 : ℝ)^4831 ≤ (11519041888493/100000000000000 : ℝ)^3807 := by
    have hnat : (1821221099 : ℕ)^4831*100000000000000^3807 ≤ 11519041888493^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821221099 10000000000 11519041888493 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268187163/2500000000 : ℝ)^4831 ≤ (1690519642541/4000000000000 : ℝ)^3807 := by
    have hnat : (1268187163 : ℕ)^4831*4000000000000^3807 ≤ 1690519642541^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268187163 2500000000 1690519642541 4000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721629547/5000000000 : ℝ)^4831 ≤ (9243593406013/20000000000000 : ℝ)^3807 := by
    have hnat : (2721629547 : ℕ)^4831*20000000000000^3807 ≤ 9243593406013^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721629547 5000000000 9243593406013 20000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1821221099/10000000000 : ℝ), (1268187163/2500000000 : ℝ), (2721629547/5000000000 : ℝ)] ![(11519041888493/100000000000000 : ℝ), (1690519642541/4000000000000 : ℝ), (9243593406013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1821221099/10000000000 : ℝ)|^4831 ≤ (11519041888493/100000000000000 : ℝ)^3807
        have hw : |(-1821221099/10000000000 : ℝ)|=(1821221099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1268187163/2500000000 : ℝ)|^4831 ≤ (1690519642541/4000000000000 : ℝ)^3807
        have hw : |(1268187163/2500000000 : ℝ)|=(1268187163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721629547/5000000000 : ℝ)|^4831 ≤ (9243593406013/20000000000000 : ℝ)^3807
        have hw : |(2721629547/5000000000 : ℝ)|=(2721629547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_9 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046157293/2000000000 : ℝ)*x 0 + (-402186891/2500000000 : ℝ)*x 1 + (2721630027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046157293/2000000000 : ℝ)^4831 ≤ (43940768451893/100000000000000 : ℝ)^3807 := by
    have hnat : (1046157293 : ℕ)^4831*100000000000000^3807 ≤ 43940768451893^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046157293 2000000000 43940768451893 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402186891/2500000000 : ℝ)^4831 ≤ (153769596281/1562500000000 : ℝ)^3807 := by
    have hnat : (402186891 : ℕ)^4831*1562500000000^3807 ≤ 153769596281^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402186891 2500000000 153769596281 1562500000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721630027/5000000000 : ℝ)^4831 ≤ (11554494343449/25000000000000 : ℝ)^3807 := by
    have hnat : (2721630027 : ℕ)^4831*25000000000000^3807 ≤ 11554494343449^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721630027 5000000000 11554494343449 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046157293/2000000000 : ℝ), (-402186891/2500000000 : ℝ), (2721630027/5000000000 : ℝ)] ![(43940768451893/100000000000000 : ℝ), (153769596281/1562500000000 : ℝ), (11554494343449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046157293/2000000000 : ℝ)|^4831 ≤ (43940768451893/100000000000000 : ℝ)^3807
        have hw : |(1046157293/2000000000 : ℝ)|=(1046157293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402186891/2500000000 : ℝ)|^4831 ≤ (153769596281/1562500000000 : ℝ)^3807
        have hw : |(-402186891/2500000000 : ℝ)|=(402186891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721630027/5000000000 : ℝ)|^4831 ≤ (11554494343449/25000000000000 : ℝ)^3807
        have hw : |(2721630027/5000000000 : ℝ)|=(2721630027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_10 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230786509/10000000000 : ℝ)*x 0 + (2721630111/5000000000 : ℝ)*x 1 + (-160874727/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230786509/10000000000 : ℝ)^4831 ≤ (43940768920931/100000000000000 : ℝ)^3807 := by
    have hnat : (5230786509 : ℕ)^4831*100000000000000^3807 ≤ 43940768920931^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230786509 10000000000 43940768920931 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721630111/5000000000 : ℝ)^4831 ≤ (46217979183949/100000000000000 : ℝ)^3807 := by
    have hnat : (2721630111 : ℕ)^4831*100000000000000^3807 ≤ 46217979183949^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721630111 5000000000 46217979183949 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160874727/1000000000 : ℝ)^4831 ≤ (984125187973/10000000000000 : ℝ)^3807 := by
    have hnat : (160874727 : ℕ)^4831*10000000000000^3807 ≤ 984125187973^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160874727 1000000000 984125187973 10000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230786509/10000000000 : ℝ), (2721630111/5000000000 : ℝ), (-160874727/1000000000 : ℝ)] ![(43940768920931/100000000000000 : ℝ), (46217979183949/100000000000000 : ℝ), (984125187973/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230786509/10000000000 : ℝ)|^4831 ≤ (43940768920931/100000000000000 : ℝ)^3807
        have hw : |(5230786509/10000000000 : ℝ)|=(5230786509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721630111/5000000000 : ℝ)|^4831 ≤ (46217979183949/100000000000000 : ℝ)^3807
        have hw : |(2721630111/5000000000 : ℝ)|=(2721630111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-160874727/1000000000 : ℝ)|^4831 ≤ (984125187973/10000000000000 : ℝ)^3807
        have hw : |(-160874727/1000000000 : ℝ)|=(160874727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_11 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (182329163/400000000 : ℝ)*x 0 + (805799009/2000000000 : ℝ)*x 1 + (2014497309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182329163/400000000 : ℝ)^4831 ≤ (36899437810461/100000000000000 : ℝ)^3807 := by
    have hnat : (182329163 : ℕ)^4831*100000000000000^3807 ≤ 36899437810461^3807*400000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182329163 400000000 36899437810461 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805799009/2000000000 : ℝ)^4831 ≤ (15775141604339/50000000000000 : ℝ)^3807 := by
    have hnat : (805799009 : ℕ)^4831*50000000000000^3807 ≤ 15775141604339^3807*2000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805799009 2000000000 15775141604339 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014497309/5000000000 : ℝ)^4831 ≤ (15775139482763/50000000000000 : ℝ)^3807 := by
    have hnat : (2014497309 : ℕ)^4831*50000000000000^3807 ≤ 15775139482763^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014497309 5000000000 15775139482763 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(182329163/400000000 : ℝ), (805799009/2000000000 : ℝ), (2014497309/5000000000 : ℝ)] ![(36899437810461/100000000000000 : ℝ), (15775141604339/50000000000000 : ℝ), (15775139482763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(182329163/400000000 : ℝ)|^4831 ≤ (36899437810461/100000000000000 : ℝ)^3807
        have hw : |(182329163/400000000 : ℝ)|=(182329163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805799009/2000000000 : ℝ)|^4831 ≤ (15775141604339/50000000000000 : ℝ)^3807
        have hw : |(805799009/2000000000 : ℝ)|=(805799009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014497309/5000000000 : ℝ)|^4831 ≤ (15775139482763/50000000000000 : ℝ)^3807
        have hw : |(2014497309/5000000000 : ℝ)|=(2014497309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_12 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-377002789/2500000000 : ℝ)*x 0 + (346885341/625000000 : ℝ)*x 1 + (2597571937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377002789/2500000000 : ℝ)^4831 ≤ (4532974711419/50000000000000 : ℝ)^3807 := by
    have hnat : (377002789 : ℕ)^4831*50000000000000^3807 ≤ 4532974711419^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377002789 2500000000 4532974711419 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346885341/625000000 : ℝ)^4831 ≤ (23686440640119/50000000000000 : ℝ)^3807 := by
    have hnat : (346885341 : ℕ)^4831*50000000000000^3807 ≤ 23686440640119^3807*625000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346885341 625000000 23686440640119 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597571937/5000000000 : ℝ)^4831 ≤ (43561169288191/100000000000000 : ℝ)^3807 := by
    have hnat : (2597571937 : ℕ)^4831*100000000000000^3807 ≤ 43561169288191^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597571937 5000000000 43561169288191 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-377002789/2500000000 : ℝ), (346885341/625000000 : ℝ), (2597571937/5000000000 : ℝ)] ![(4532974711419/50000000000000 : ℝ), (23686440640119/50000000000000 : ℝ), (43561169288191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-377002789/2500000000 : ℝ)|^4831 ≤ (4532974711419/50000000000000 : ℝ)^3807
        have hw : |(-377002789/2500000000 : ℝ)|=(377002789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346885341/625000000 : ℝ)|^4831 ≤ (23686440640119/50000000000000 : ℝ)^3807
        have hw : |(346885341/625000000 : ℝ)|=(346885341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597571937/5000000000 : ℝ)|^4831 ≤ (43561169288191/100000000000000 : ℝ)^3807
        have hw : |(2597571937/5000000000 : ℝ)|=(2597571937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_13 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401608781/10000000000 : ℝ)*x 0 + (-1714480243/10000000000 : ℝ)*x 1 + (2597571791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401608781/10000000000 : ℝ)^4831 ≤ (45769659252057/100000000000000 : ℝ)^3807 := by
    have hnat : (5401608781 : ℕ)^4831*100000000000000^3807 ≤ 45769659252057^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401608781 10000000000 45769659252057 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1714480243/10000000000 : ℝ)^4831 ≤ (10669174557959/100000000000000 : ℝ)^3807 := by
    have hnat : (1714480243 : ℕ)^4831*100000000000000^3807 ≤ 10669174557959^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714480243 10000000000 10669174557959 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597571791/5000000000 : ℝ)^4831 ≤ (5445145772651/12500000000000 : ℝ)^3807 := by
    have hnat : (2597571791 : ℕ)^4831*12500000000000^3807 ≤ 5445145772651^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597571791 5000000000 5445145772651 12500000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401608781/10000000000 : ℝ), (-1714480243/10000000000 : ℝ), (2597571791/5000000000 : ℝ)] ![(45769659252057/100000000000000 : ℝ), (10669174557959/100000000000000 : ℝ), (5445145772651/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401608781/10000000000 : ℝ)|^4831 ≤ (45769659252057/100000000000000 : ℝ)^3807
        have hw : |(5401608781/10000000000 : ℝ)|=(5401608781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1714480243/10000000000 : ℝ)|^4831 ≤ (10669174557959/100000000000000 : ℝ)^3807
        have hw : |(-1714480243/10000000000 : ℝ)|=(1714480243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597571791/5000000000 : ℝ)|^4831 ≤ (5445145772651/12500000000000 : ℝ)^3807
        have hw : |(2597571791/5000000000 : ℝ)|=(2597571791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_14 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540160903/1000000000 : ℝ)*x 0 + (1298785639/2500000000 : ℝ)*x 1 + (-857240643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540160903/1000000000 : ℝ)^4831 ≤ (1830786477177/4000000000000 : ℝ)^3807 := by
    have hnat : (540160903 : ℕ)^4831*4000000000000^3807 ≤ 1830786477177^3807*1000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540160903 1000000000 1830786477177 4000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298785639/2500000000 : ℝ)^4831 ≤ (10890288816051/25000000000000 : ℝ)^3807 := by
    have hnat : (1298785639 : ℕ)^4831*25000000000000^3807 ≤ 10890288816051^3807*2500000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298785639 2500000000 10890288816051 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857240643/5000000000 : ℝ)^4831 ≤ (2667295698587/25000000000000 : ℝ)^3807 := by
    have hnat : (857240643 : ℕ)^4831*25000000000000^3807 ≤ 2667295698587^3807*5000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857240643 5000000000 2667295698587 25000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540160903/1000000000 : ℝ), (1298785639/2500000000 : ℝ), (-857240643/5000000000 : ℝ)] ![(1830786477177/4000000000000 : ℝ), (10890288816051/25000000000000 : ℝ), (2667295698587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540160903/1000000000 : ℝ)|^4831 ≤ (1830786477177/4000000000000 : ℝ)^3807
        have hw : |(540160903/1000000000 : ℝ)|=(540160903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298785639/2500000000 : ℝ)|^4831 ≤ (10890288816051/25000000000000 : ℝ)^3807
        have hw : |(1298785639/2500000000 : ℝ)|=(1298785639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857240643/5000000000 : ℝ)|^4831 ≤ (2667295698587/25000000000000 : ℝ)^3807
        have hw : |(-857240643/5000000000 : ℝ)|=(857240643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1628_box_15 (p : ℝ) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (120483859/312500000 : ℝ)*x 0 + (4380357129/10000000000 : ℝ)*x 1 + (273772213/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120483859/312500000 : ℝ)^4831 ≤ (14918085300863/50000000000000 : ℝ)^3807 := by
    have hnat : (120483859 : ℕ)^4831*50000000000000^3807 ≤ 14918085300863^3807*312500000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120483859 312500000 14918085300863 50000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4380357129/10000000000 : ℝ)^4831 ≤ (35081923439731/100000000000000 : ℝ)^3807 := by
    have hnat : (4380357129 : ℕ)^4831*100000000000000^3807 ≤ 35081923439731^3807*10000000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380357129 10000000000 35081923439731 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273772213/625000000 : ℝ)^4831 ≤ (35081905948963/100000000000000 : ℝ)^3807 := by
    have hnat : (273772213 : ℕ)^4831*100000000000000^3807 ≤ 35081905948963^3807*625000000^4831 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273772213 625000000 35081905948963 100000000000000 4831 3807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4831/1024 : ℝ)) 4831 3807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(120483859/312500000 : ℝ), (4380357129/10000000000 : ℝ), (273772213/625000000 : ℝ)] ![(14918085300863/50000000000000 : ℝ), (35081923439731/100000000000000 : ℝ), (35081905948963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(120483859/312500000 : ℝ)|^4831 ≤ (14918085300863/50000000000000 : ℝ)^3807
        have hw : |(120483859/312500000 : ℝ)|=(120483859/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4380357129/10000000000 : ℝ)|^4831 ≤ (35081923439731/100000000000000 : ℝ)^3807
        have hw : |(4380357129/10000000000 : ℝ)|=(4380357129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273772213/625000000 : ℝ)|^4831 ≤ (35081905948963/100000000000000 : ℝ)^3807
        have hw : |(273772213/625000000 : ℝ)|=(273772213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1628_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16309/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64981/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58389/100000 : ℝ) ∧ (40393/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88007/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16309/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2637/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16309/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2637/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16309/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2637/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16309/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2637/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16309/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2637/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16309/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2637/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2637/25000 : ℝ) ^ (4827/1024 : ℝ) ≤ (497031234807403/20000000000000000000 : ℝ) := by
    have hpowers : (2637/25000 : ℝ)^4827 ≤ (497031234807403/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2637 : ℕ)^4827*20000000000000000000^1024 ≤ 497031234807403^1024*25000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2637 25000 497031234807403 20000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2637/25000 : ℝ)) (X := (497031234807403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16309/100000 : ℝ) ^ (4827/1024 : ℝ) ≤ (4846487027868159/25000000000000000000 : ℝ) := by
    have hpowers : (16309/100000 : ℝ)^4827 ≤ (4846487027868159/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16309 : ℕ)^4827*25000000000000000000^1024 ≤ 4846487027868159^1024*100000^4827 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16309 100000 4846487027868159 25000000000000000000 4827 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16309/100000 : ℝ)) (X := (4846487027868159/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000497031234807403/10000000000000000000 : ℝ) ≤ (2000021087632879/2000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (10000497031234807403/10000000000000000000 : ℝ)^1024 ≤ (2000021087632879/2000000000000000 : ℝ)^4827 := by
      have hnat : (10000497031234807403 : ℕ)^1024*2000000000000000^4827 ≤ 2000021087632879^4827*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000497031234807403 10000000000000000000 2000021087632879 2000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000021087632879/2000000000000000 : ℝ)) (X := (10000497031234807403/10000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021871104285509651/100000000000000000000 : ℝ) ≤ (5000231966868349/5000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (100021871104285509651/100000000000000000000 : ℝ)^1024 ≤ (5000231966868349/5000000000000000 : ℝ)^4827 := by
      have hnat : (100021871104285509651 : ℕ)^1024*5000000000000000^4827 ≤ 5000231966868349^4827*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021871104285509651 100000000000000000000 5000231966868349 5000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000231966868349/5000000000000000 : ℝ)) (X := (100021871104285509651/100000000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504846487027868159/12500000000000000000 : ℝ) ≤ (10000822429309001/10000000000000000 : ℝ) ^ (4827/1024 : ℝ) := by
    have hpowers : (12504846487027868159/12500000000000000000 : ℝ)^1024 ≤ (10000822429309001/10000000000000000 : ℝ)^4827 := by
      have hnat : (12504846487027868159 : ℕ)^1024*10000000000000000^4827 ≤ 10000822429309001^4827*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504846487027868159 12500000000000000000 10000822429309001 10000000000000000 1024 4827 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000822429309001/10000000000000000 : ℝ)) (X := (12504846487027868159/12500000000000000000 : ℝ)) (by norm_num) 4827 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(497031234807403/20000000000000000000 : ℝ) ≤ ((57603044606671775507/57610000000000000000 : ℝ)+2*(358495572303/576100000000000 : ℝ)*(2637/25000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (57603044606671775507/57610000000000000000 : ℝ)+2*(358495572303/576100000000000 : ℝ)*(2637/25000 : ℝ)=(2000021087632879/2000000000000000 : ℝ) by norm_num, show 1+2*(497031234807403/20000000000000000000 : ℝ)=(10000497031234807403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4846487027868159/25000000000000000000 : ℝ)+(497031234807403/20000000000000000000 : ℝ) ≤ ((57603044606671775507/57610000000000000000 : ℝ)+(358495572303/576100000000000 : ℝ)*((16309/100000 : ℝ)+(2637/25000 : ℝ)))^(4827/1024 : ℝ) := by
    rw [show (57603044606671775507/57610000000000000000 : ℝ)+(358495572303/576100000000000 : ℝ)*((16309/100000 : ℝ)+(2637/25000 : ℝ))=(5000231966868349/5000000000000000 : ℝ) by norm_num, show 1+(4846487027868159/25000000000000000000 : ℝ)+(497031234807403/20000000000000000000 : ℝ)=(100021871104285509651/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4846487027868159/25000000000000000000 : ℝ) ≤ ((57603044606671775507/57610000000000000000 : ℝ)+2*(358495572303/576100000000000 : ℝ)*(16309/100000 : ℝ))^(4827/1024 : ℝ) := by
    rw [show (57603044606671775507/57610000000000000000 : ℝ)+2*(358495572303/576100000000000 : ℝ)*(16309/100000 : ℝ)=(10000822429309001/10000000000000000 : ℝ) by norm_num, show 1+2*(4846487027868159/25000000000000000000 : ℝ)=(12504846487027868159/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57603044606671775507/57610000000000000000 : ℝ)*(X 1 0+X 2 0)+(358495572303/576100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (16309/100000 : ℝ)) (c := (57603044606671775507/57610000000000000000 : ℝ)) (alpha := (358495572303/576100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57603044606671775507/57610000000000000000 : ℝ)*(X 0 1+X 2 1)+(358495572303/576100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (16309/100000 : ℝ)) (c := (57603044606671775507/57610000000000000000 : ℝ)) (alpha := (358495572303/576100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57603044606671775507/57610000000000000000 : ℝ)*(X 0 2+X 1 2)+(358495572303/576100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4827/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (16309/100000 : ℝ)) (c := (57603044606671775507/57610000000000000000 : ℝ)) (alpha := (358495572303/576100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1393864811/10000000000 : ℝ)*X 0 0+(1353383307/2500000000 : ℝ)*X 0 1+(5413533253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((164101663/312500000 : ℝ)*X 1 0+(-405460877/2500000000 : ℝ)*X 1 1+(1353383347/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251253217/10000000000 : ℝ)*X 2 0+(5413533393/10000000000 : ℝ)*X 2 1+(-1621843501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2238165863/5000000000 : ℝ)*X 0 0+(254447733/625000000 : ℝ)*X 0 1+(814232747/2000000000 : ℝ)*X 0 2+(2238165863/5000000000 : ℝ)*X 1 0+(254447733/625000000 : ℝ)*X 1 1+(814232747/2000000000 : ℝ)*X 1 2+(2238165863/5000000000 : ℝ)*X 2 0+(254447733/625000000 : ℝ)*X 2 1+(814232747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1936848887/10000000000 : ℝ)*X 0 0+(5214999893/10000000000 : ℝ)*X 0 1+(2607499959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((673491421/1250000000 : ℝ)*X 1 0+(-21329043/125000000 : ℝ)*X 1 1+(2607499989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1077586277/2000000000 : ℝ)*X 2 0+(162968749/312500000 : ℝ)*X 2 1+(-170632343/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3913412609/10000000000 : ℝ)*X 0 0+(4352288599/10000000000 : ℝ)*X 0 1+(870457733/2000000000 : ℝ)*X 0 2+(3913412609/10000000000 : ℝ)*X 1 0+(4352288599/10000000000 : ℝ)*X 1 1+(870457733/2000000000 : ℝ)*X 1 2+(3913412609/10000000000 : ℝ)*X 2 0+(4352288599/10000000000 : ℝ)*X 2 1+(870457733/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1821221099/10000000000 : ℝ)*X 0 0+(1268187163/2500000000 : ℝ)*X 0 1+(2721629547/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046157293/2000000000 : ℝ)*X 1 0+(-402186891/2500000000 : ℝ)*X 1 1+(2721630027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230786509/10000000000 : ℝ)*X 2 0+(2721630111/5000000000 : ℝ)*X 2 1+(-160874727/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((182329163/400000000 : ℝ)*X 0 0+(805799009/2000000000 : ℝ)*X 0 1+(2014497309/5000000000 : ℝ)*X 0 2+(182329163/400000000 : ℝ)*X 1 0+(805799009/2000000000 : ℝ)*X 1 1+(2014497309/5000000000 : ℝ)*X 1 2+(182329163/400000000 : ℝ)*X 2 0+(805799009/2000000000 : ℝ)*X 2 1+(2014497309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-377002789/2500000000 : ℝ)*X 0 0+(346885341/625000000 : ℝ)*X 0 1+(2597571937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5401608781/10000000000 : ℝ)*X 1 0+(-1714480243/10000000000 : ℝ)*X 1 1+(2597571791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((540160903/1000000000 : ℝ)*X 2 0+(1298785639/2500000000 : ℝ)*X 2 1+(-857240643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((120483859/312500000 : ℝ)*X 0 0+(4380357129/10000000000 : ℝ)*X 0 1+(273772213/625000000 : ℝ)*X 0 2+(120483859/312500000 : ℝ)*X 1 0+(4380357129/10000000000 : ℝ)*X 1 1+(273772213/625000000 : ℝ)*X 1 2+(120483859/312500000 : ℝ)*X 2 0+(4380357129/10000000000 : ℝ)*X 2 1+(273772213/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1628_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64981/100000 : ℝ) ≤ (-1871708842134953787020068038733161/2880500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (688073/100000000000000 : ℝ)*(upper0) + (66071/25000000000000 : ℝ)*(upper2) + (2187147/50000000000000 : ℝ)*(upper3) + (3056183/20000000000000 : ℝ)*(upper5) + (1716780440349841/100000000000000 : ℝ)*(major0) + (1716780440349841/100000000000000 : ℝ)*(major1) + (1716780440349841/100000000000000 : ℝ)*(major2) + (71066659/100000000000000 : ℝ)*(sp3) + (38727800974741/1562500000000 : ℝ)*(sp4) + (3872771837241/156250000000 : ℝ)*(sp5) + (1239288624891651/50000000000000 : ℝ)*(sp6) + (244160270924343/25000000000000 : ℝ)*(sp7) + (5286549183/100000000000000 : ℝ)*(sp13) + (1006300061/50000000000000 : ℝ)*(sp14) + (976641154764031/100000000000000 : ℝ)*(f.failure) + (38727800974741/1562500000000 : ℝ)*(f.sum) + (66163930482847/28805000000000000000000000000 : ℝ)*base66 + (1772426464607793659/823000000000000000000000000000000 : ℝ)*base68 + (1381491611797206341/823000000000000000000000000000000 : ℝ)*base69 + (1338659195693206341/823000000000000000000000000000000 : ℝ)*base71 + (43812033872367/7201250000000000000000000000 : ℝ)*base73 + (4281018553735206341/823000000000000000000000000000000 : ℝ)*base75 + (3865514383707793659/823000000000000000000000000000000 : ℝ)*base78 + (2453717598264206341/823000000000000000000000000000000 : ℝ)*base79 + (70431983785229/14402500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (67215071/10000000000000000000000 : ℝ)*base90 + (67215071/10000000000000000000000 : ℝ)*base92 + (67215071/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58389/100000 : ℝ) ≤ (840976441114885187219114743571907/1440250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18036687/100000000000000 : ℝ)*(upper3) + (246447/25000000000000 : ℝ)*(upper4) + (1004893/5000000000000 : ℝ)*(upper5) + (1804087495345067/100000000000000 : ℝ)*(major0) + (1804087495345067/100000000000000 : ℝ)*(major1) + (1804087495345067/100000000000000 : ℝ)*(major2) + (320300355949871/12500000000000 : ℝ)*(sp0) + (1251172851969/48828125000 : ℝ)*(sp1) + (1281200973727807/50000000000000 : ℝ)*(sp2) + (3207211855777/312500000000 : ℝ)*(sp3) + (48769373/5000000000000 : ℝ)*(sp5) + (514382179/50000000000000 : ℝ)*(sp6) + (276241269/50000000000000 : ℝ)*(sp7) + (32155251/25000000000000 : ℝ)*(sp12) + (1026308346331177/100000000000000 : ℝ)*(f.failure) + (640600744054993/25000000000000 : ℝ)*(f.sum) + (226838961281749/28805000000000000000000000000 : ℝ)*base66 + (167752118877710567/823000000000000000000000000000000 : ℝ)*base67 + (9047670107902289433/823000000000000000000000000000000 : ℝ)*base70 + (8549066737534289433/823000000000000000000000000000000 : ℝ)*base72 + (42802308324071/28805000000000000000000000000 : ℝ)*base73 + (4500244621830289433/823000000000000000000000000000000 : ℝ)*base76 + (4610667884842289433/823000000000000000000000000000000 : ℝ)*base78 + (4128729518836289433/823000000000000000000000000000000 : ℝ)*base80 + (194182473709579/28805000000000000000000000000 : ℝ)*base82 + (15574857/10000000000000000000000 : ℝ)*base90 + (15574857/10000000000000000000000 : ℝ)*base92 + (15574857/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40393/50000 : ℝ) ≤ (290888458806976941522723738840063/360062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1813157/100000000000000 : ℝ)*(upper3) + (83312521/100000000000000 : ℝ)*(upper4) + (10817533/100000000000000 : ℝ)*(lower5) + (476186137663003/25000000000000 : ℝ)*(major0) + (476186137663003/25000000000000 : ℝ)*(major1) + (476186137663003/25000000000000 : ℝ)*(major2) + (4540651549/50000000000000 : ℝ)*(sp0) + (4781645879/5000000000000 : ℝ)*(sp1) + (41771873/32000000000 : ℝ)*(sp2) + (4410145919/12500000000000 : ℝ)*(sp3) + (2698980499634517/100000000000000 : ℝ)*(sp8) + (1349446974010017/50000000000000 : ℝ)*(sp9) + (2698859043834489/100000000000000 : ℝ)*(sp10) + (541767398946539/50000000000000 : ℝ)*(sp11) + (108357007906043/10000000000000 : ℝ)*(f.failure) + (1349494790468807/50000000000000 : ℝ)*(f.sum) + (81654707785869/28805000000000000000000000000 : ℝ)*base66 + (1810394764597447497/205750000000000000000000000000000 : ℝ)*base68 + (2241097642948947497/205750000000000000000000000000000 : ℝ)*base70 + (1339301601660947497/205750000000000000000000000000000 : ℝ)*base72 + (6865469765557/14402500000000000000000000000 : ℝ)*base74 + (1153630190281947497/205750000000000000000000000000000 : ℝ)*base76 + (127050885257052503/205750000000000000000000000000000 : ℝ)*base77 + (541079448063697497/205750000000000000000000000000000 : ℝ)*base80 + (61315627714909/28805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (227163/1000000000000000000000 : ℝ)*base90 + (227163/1000000000000000000000 : ℝ)*base92 + (227163/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88007/100000 : ℝ) ≤ (-63373970731839069925679434177389/72012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10727257/1562500000000 : ℝ)*(upper3) + (47570697/100000000000000 : ℝ)*(lower4) + (272348799/100000000000000 : ℝ)*(upper5) + (48693362902403/2500000000000 : ℝ)*(major0) + (48693362902403/2500000000000 : ℝ)*(major1) + (48693362902403/2500000000000 : ℝ)*(major2) + (7808949887/20000000000000 : ℝ)*(sp4) + (426221243401/100000000000000 : ℝ)*(sp5) + (256136511517/50000000000000 : ℝ)*(sp6) + (114361927077/50000000000000 : ℝ)*(sp7) + (1408369253932259/50000000000000 : ℝ)*(sp12) + (352043916421319/12500000000000 : ℝ)*(sp13) + (1408132639795459/50000000000000 : ℝ)*(sp14) + (1107797464157543/100000000000000 : ℝ)*(sp15) + (1108026188011697/100000000000000 : ℝ)*(f.failure) + (2816777552613953/100000000000000 : ℝ)*(f.sum) + (881468386567/1152200000000000000000000000 : ℝ)*base65 + (123660645555691903/20575000000000000000000000000000 : ℝ)*base67 + (111199374996191903/20575000000000000000000000000000 : ℝ)*base69 + (123882186991641903/20575000000000000000000000000000 : ℝ)*base71 + (1214506496447/1152200000000000000000000000 : ℝ)*base73 + (19249013202691903/20575000000000000000000000000000 : ℝ)*base75 + (156135722620391903/20575000000000000000000000000000 : ℝ)*base77 + (163212612937916903/20575000000000000000000000000000 : ℝ)*base79 + (2887248887137/2880500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (39307823/10000000000000000000000 : ℝ)*base89 + (39307823/10000000000000000000000 : ℝ)*base91 + (39307823/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1628_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16309/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64981/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58389/100000 : ℝ) else (40393/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88007/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1628_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1628_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16309/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64981/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58389/100000 : ℝ) else (40393/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88007/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1628_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4827/1024 : ℝ) ≤ p) (hpb : p ≤ (4831/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175784159/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16309/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64981/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58389/100000 : ℝ) else (40393/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88007/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1628_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
