-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1701_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:25.214585+00:00
-- url     : https://prove2.me/submissions/c354ef77-c76e-4d1b-ac0c-396f9c32c1c7

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
theorem support_rectangle_w1701_s3_0 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-289053051/2000000000 : ℝ)*x 0 + (2737930593/5000000000 : ℝ)*x 1 + (256853863/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (289053051/2000000000 : ℝ)^5231 ≤ (9025589225353/100000000000000 : ℝ)^4207 := by
    have hnat : (289053051 : ℕ)^5231*100000000000000^4207 ≤ 9025589225353^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289053051 2000000000 9025589225353 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737930593/5000000000 : ℝ)^5231 ≤ (23646166804429/50000000000000 : ℝ)^4207 := by
    have hnat : (2737930593 : ℕ)^5231*50000000000000^4207 ≤ 23646166804429^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737930593 5000000000 23646166804429 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256853863/500000000 : ℝ)^5231 ≤ (21841038576261/50000000000000 : ℝ)^4207 := by
    have hnat : (256853863 : ℕ)^5231*50000000000000^4207 ≤ 21841038576261^4207*500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256853863 500000000 21841038576261 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-289053051/2000000000 : ℝ), (2737930593/5000000000 : ℝ), (256853863/500000000 : ℝ)] ![(9025589225353/100000000000000 : ℝ), (23646166804429/50000000000000 : ℝ), (21841038576261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-289053051/2000000000 : ℝ)|^5231 ≤ (9025589225353/100000000000000 : ℝ)^4207
        have hw : |(-289053051/2000000000 : ℝ)|=(289053051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737930593/5000000000 : ℝ)|^5231 ≤ (23646166804429/50000000000000 : ℝ)^4207
        have hw : |(2737930593/5000000000 : ℝ)|=(2737930593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256853863/500000000 : ℝ)|^5231 ≤ (21841038576261/50000000000000 : ℝ)^4207
        have hw : |(256853863/500000000 : ℝ)|=(256853863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s3_1 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346539171/10000000000 : ℝ)*x 0 + (-50658401/312500000 : ℝ)*x 1 + (256853863/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346539171/10000000000 : ℝ)^5231 ≤ (45907602647641/100000000000000 : ℝ)^4207 := by
    have hnat : (5346539171 : ℕ)^5231*100000000000000^4207 ≤ 45907602647641^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346539171 10000000000 45907602647641 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50658401/312500000 : ℝ)^5231 ≤ (2602580047241/25000000000000 : ℝ)^4207 := by
    have hnat : (50658401 : ℕ)^5231*25000000000000^4207 ≤ 2602580047241^4207*312500000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50658401 312500000 2602580047241 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256853863/500000000 : ℝ)^5231 ≤ (21841038576261/50000000000000 : ℝ)^4207 := by
    have hnat : (256853863 : ℕ)^5231*50000000000000^4207 ≤ 21841038576261^4207*500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256853863 500000000 21841038576261 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346539171/10000000000 : ℝ), (-50658401/312500000 : ℝ), (256853863/500000000 : ℝ)] ![(45907602647641/100000000000000 : ℝ), (2602580047241/25000000000000 : ℝ), (21841038576261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346539171/10000000000 : ℝ)|^5231 ≤ (45907602647641/100000000000000 : ℝ)^4207
        have hw : |(5346539171/10000000000 : ℝ)|=(5346539171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50658401/312500000 : ℝ)|^5231 ≤ (2602580047241/25000000000000 : ℝ)^4207
        have hw : |(-50658401/312500000 : ℝ)|=(50658401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256853863/500000000 : ℝ)|^5231 ≤ (21841038576261/50000000000000 : ℝ)^4207
        have hw : |(256853863/500000000 : ℝ)|=(256853863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s3_2 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346539171/10000000000 : ℝ)*x 0 + (256853863/500000000 : ℝ)*x 1 + (-50658401/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346539171/10000000000 : ℝ)^5231 ≤ (45907602647641/100000000000000 : ℝ)^4207 := by
    have hnat : (5346539171 : ℕ)^5231*100000000000000^4207 ≤ 45907602647641^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346539171 10000000000 45907602647641 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256853863/500000000 : ℝ)^5231 ≤ (21841038576261/50000000000000 : ℝ)^4207 := by
    have hnat : (256853863 : ℕ)^5231*50000000000000^4207 ≤ 21841038576261^4207*500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256853863 500000000 21841038576261 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50658401/312500000 : ℝ)^5231 ≤ (2602580047241/25000000000000 : ℝ)^4207 := by
    have hnat : (50658401 : ℕ)^5231*25000000000000^4207 ≤ 2602580047241^4207*312500000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50658401 312500000 2602580047241 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346539171/10000000000 : ℝ), (256853863/500000000 : ℝ), (-50658401/312500000 : ℝ)] ![(45907602647641/100000000000000 : ℝ), (21841038576261/50000000000000 : ℝ), (2602580047241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346539171/10000000000 : ℝ)|^5231 ≤ (45907602647641/100000000000000 : ℝ)^4207
        have hw : |(5346539171/10000000000 : ℝ)|=(5346539171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256853863/500000000 : ℝ)|^5231 ≤ (21841038576261/50000000000000 : ℝ)^4207
        have hw : |(256853863/500000000 : ℝ)|=(256853863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50658401/312500000 : ℝ)|^5231 ≤ (2602580047241/25000000000000 : ℝ)^4207
        have hw : |(-50658401/312500000 : ℝ)|=(50658401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s3_3 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2058215971/5000000000 : ℝ)*x 0 + (1826801719/5000000000 : ℝ)*x 1 + (2307837803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058215971/5000000000 : ℝ)^5231 ≤ (33166057688757/100000000000000 : ℝ)^4207 := by
    have hnat : (2058215971 : ℕ)^5231*100000000000000^4207 ≤ 33166057688757^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058215971 5000000000 33166057688757 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1826801719/5000000000 : ℝ)^5231 ≤ (28594737492181/100000000000000 : ℝ)^4207 := by
    have hnat : (1826801719 : ℕ)^5231*100000000000000^4207 ≤ 28594737492181^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826801719 5000000000 28594737492181 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2307837803/5000000000 : ℝ)^5231 ≤ (3823920480927/10000000000000 : ℝ)^4207 := by
    have hnat : (2307837803 : ℕ)^5231*10000000000000^4207 ≤ 3823920480927^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307837803 5000000000 3823920480927 10000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2058215971/5000000000 : ℝ), (1826801719/5000000000 : ℝ), (2307837803/5000000000 : ℝ)] ![(33166057688757/100000000000000 : ℝ), (28594737492181/100000000000000 : ℝ), (3823920480927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2058215971/5000000000 : ℝ)|^5231 ≤ (33166057688757/100000000000000 : ℝ)^4207
        have hw : |(2058215971/5000000000 : ℝ)|=(2058215971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1826801719/5000000000 : ℝ)|^5231 ≤ (28594737492181/100000000000000 : ℝ)^4207
        have hw : |(1826801719/5000000000 : ℝ)|=(1826801719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2307837803/5000000000 : ℝ)|^5231 ≤ (3823920480927/10000000000000 : ℝ)^4207
        have hw : |(2307837803/5000000000 : ℝ)|=(2307837803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s3_4 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1445420603/10000000000 : ℝ)*x 0 + (2570399873/5000000000 : ℝ)*x 1 + (2736041573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445420603/10000000000 : ℝ)^5231 ≤ (1763045999/19531250000 : ℝ)^4207 := by
    have hnat : (1445420603 : ℕ)^5231*19531250000^4207 ≤ 1763045999^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445420603 10000000000 1763045999 19531250000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570399873/5000000000 : ℝ)^5231 ≤ (21860719286213/50000000000000 : ℝ)^4207 := by
    have hnat : (2570399873 : ℕ)^5231*50000000000000^4207 ≤ 21860719286213^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570399873 5000000000 21860719286213 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736041573/5000000000 : ℝ)^5231 ≤ (5906470736113/12500000000000 : ℝ)^4207 := by
    have hnat : (2736041573 : ℕ)^5231*12500000000000^4207 ≤ 5906470736113^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736041573 5000000000 5906470736113 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1445420603/10000000000 : ℝ), (2570399873/5000000000 : ℝ), (2736041573/5000000000 : ℝ)] ![(1763045999/19531250000 : ℝ), (21860719286213/50000000000000 : ℝ), (5906470736113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1445420603/10000000000 : ℝ)|^5231 ≤ (1763045999/19531250000 : ℝ)^4207
        have hw : |(-1445420603/10000000000 : ℝ)|=(1445420603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570399873/5000000000 : ℝ)|^5231 ≤ (21860719286213/50000000000000 : ℝ)^4207
        have hw : |(2570399873/5000000000 : ℝ)|=(2570399873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736041573/5000000000 : ℝ)|^5231 ≤ (5906470736113/12500000000000 : ℝ)^4207
        have hw : |(2736041573/5000000000 : ℝ)|=(2736041573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s3_5 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255888819/10000000000 : ℝ)*x 0 + (-1286062949/10000000000 : ℝ)*x 1 + (684010393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255888819/10000000000 : ℝ)^5231 ≤ (44941790588369/100000000000000 : ℝ)^4207 := by
    have hnat : (5255888819 : ℕ)^5231*100000000000000^4207 ≤ 44941790588369^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255888819 10000000000 44941790588369 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286062949/10000000000 : ℝ)^5231 ≤ (7806443530539/100000000000000 : ℝ)^4207 := by
    have hnat : (1286062949 : ℕ)^5231*100000000000000^4207 ≤ 7806443530539^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286062949 10000000000 7806443530539 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684010393/1250000000 : ℝ)^5231 ≤ (4725176586743/10000000000000 : ℝ)^4207 := by
    have hnat : (684010393 : ℕ)^5231*10000000000000^4207 ≤ 4725176586743^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684010393 1250000000 4725176586743 10000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255888819/10000000000 : ℝ), (-1286062949/10000000000 : ℝ), (684010393/1250000000 : ℝ)] ![(44941790588369/100000000000000 : ℝ), (7806443530539/100000000000000 : ℝ), (4725176586743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255888819/10000000000 : ℝ)|^5231 ≤ (44941790588369/100000000000000 : ℝ)^4207
        have hw : |(5255888819/10000000000 : ℝ)|=(5255888819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1286062949/10000000000 : ℝ)|^5231 ≤ (7806443530539/100000000000000 : ℝ)^4207
        have hw : |(-1286062949/10000000000 : ℝ)|=(1286062949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684010393/1250000000 : ℝ)|^5231 ≤ (4725176586743/10000000000000 : ℝ)^4207
        have hw : |(684010393/1250000000 : ℝ)|=(684010393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s3_6 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051177763/2000000000 : ℝ)*x 0 + (109441663/200000000 : ℝ)*x 1 + (-643031473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051177763/2000000000 : ℝ)^5231 ≤ (44941790545841/100000000000000 : ℝ)^4207 := by
    have hnat : (1051177763 : ℕ)^5231*100000000000000^4207 ≤ 44941790545841^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051177763 2000000000 44941790545841 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109441663/200000000 : ℝ)^5231 ≤ (47251765931851/100000000000000 : ℝ)^4207 := by
    have hnat : (109441663 : ℕ)^5231*100000000000000^4207 ≤ 47251765931851^4207*200000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109441663 200000000 47251765931851 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643031473/5000000000 : ℝ)^5231 ≤ (975805438487/12500000000000 : ℝ)^4207 := by
    have hnat : (643031473 : ℕ)^5231*12500000000000^4207 ≤ 975805438487^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643031473 5000000000 975805438487 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051177763/2000000000 : ℝ), (109441663/200000000 : ℝ), (-643031473/5000000000 : ℝ)] ![(44941790545841/100000000000000 : ℝ), (47251765931851/100000000000000 : ℝ), (975805438487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051177763/2000000000 : ℝ)|^5231 ≤ (44941790545841/100000000000000 : ℝ)^4207
        have hw : |(1051177763/2000000000 : ℝ)|=(1051177763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109441663/200000000 : ℝ)|^5231 ≤ (47251765931851/100000000000000 : ℝ)^4207
        have hw : |(109441663/200000000 : ℝ)|=(109441663/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-643031473/5000000000 : ℝ)|^5231 ≤ (975805438487/12500000000000 : ℝ)^4207
        have hw : |(-643031473/5000000000 : ℝ)|=(643031473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s3_7 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4116873097/10000000000 : ℝ)*x 0 + (4605104557/10000000000 : ℝ)*x 1 + (458041531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116873097/10000000000 : ℝ)^5231 ≤ (33170477278839/100000000000000 : ℝ)^4207 := by
    have hnat : (4116873097 : ℕ)^5231*100000000000000^4207 ≤ 33170477278839^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116873097 10000000000 33170477278839 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4605104557/10000000000 : ℝ)^5231 ≤ (38130341199463/100000000000000 : ℝ)^4207 := by
    have hnat : (4605104557 : ℕ)^5231*100000000000000^4207 ≤ 38130341199463^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605104557 10000000000 38130341199463 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458041531/1250000000 : ℝ)^5231 ≤ (1793698843827/6250000000000 : ℝ)^4207 := by
    have hnat : (458041531 : ℕ)^5231*6250000000000^4207 ≤ 1793698843827^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458041531 1250000000 1793698843827 6250000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116873097/10000000000 : ℝ), (4605104557/10000000000 : ℝ), (458041531/1250000000 : ℝ)] ![(33170477278839/100000000000000 : ℝ), (38130341199463/100000000000000 : ℝ), (1793698843827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116873097/10000000000 : ℝ)|^5231 ≤ (33170477278839/100000000000000 : ℝ)^4207
        have hw : |(4116873097/10000000000 : ℝ)|=(4116873097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4605104557/10000000000 : ℝ)|^5231 ≤ (38130341199463/100000000000000 : ℝ)^4207
        have hw : |(4605104557/10000000000 : ℝ)|=(4605104557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(458041531/1250000000 : ℝ)|^5231 ≤ (1793698843827/6250000000000 : ℝ)^4207
        have hw : |(458041531/1250000000 : ℝ)|=(458041531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1701_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4967/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17157/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9921/100000 : ℝ) ^ (5223/1024 : ℝ) ≤ (761806786703771/100000000000000000000 : ℝ) := by
    have hpowers : (9921/100000 : ℝ)^5223 ≤ (761806786703771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9921 : ℕ)^5223*100000000000000000000^1024 ≤ 761806786703771^1024*100000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9921 100000 761806786703771 100000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9921/100000 : ℝ)) (X := (761806786703771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17173/100000 : ℝ) ^ (5223/1024 : ℝ) ≤ (3127570750914099/25000000000000000000 : ℝ) := by
    have hpowers : (17173/100000 : ℝ)^5223 ≤ (3127570750914099/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17173 : ℕ)^5223*25000000000000000000^1024 ≤ 3127570750914099^1024*100000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17173 100000 3127570750914099 25000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17173/100000 : ℝ)) (X := (3127570750914099/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000761806786703771/50000000000000000000 : ℝ) ≤ (5000014935580547/5000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (50000761806786703771/50000000000000000000 : ℝ)^1024 ≤ (5000014935580547/5000000000000000 : ℝ)^5223 := by
      have hnat : (50000761806786703771 : ℕ)^1024*5000000000000000^5223 ≤ 5000014935580547^5223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000761806786703771 50000000000000000000 5000014935580547 5000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000014935580547/5000000000000000 : ℝ)) (X := (50000761806786703771/50000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013272089790360167/100000000000000000000 : ℝ) ≤ (5000130096639311/5000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (100013272089790360167/100000000000000000000 : ℝ)^1024 ≤ (5000130096639311/5000000000000000 : ℝ)^5223 := by
      have hnat : (100013272089790360167 : ℕ)^1024*5000000000000000^5223 ≤ 5000130096639311^5223*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013272089790360167 100000000000000000000 5000130096639311 5000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000130096639311/5000000000000000 : ℝ)) (X := (100013272089790360167/100000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503127570750914099/12500000000000000000 : ℝ) ≤ (200009810307923/200000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (12503127570750914099/12500000000000000000 : ℝ)^1024 ≤ (200009810307923/200000000000000 : ℝ)^5223 := by
      have hnat : (12503127570750914099 : ℕ)^1024*200000000000000^5223 ≤ 200009810307923^5223*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503127570750914099 12500000000000000000 200009810307923 200000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200009810307923/200000000000000 : ℝ)) (X := (12503127570750914099/12500000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(761806786703771/100000000000000000000 : ℝ) ≤ ((9064455821775532889/9065000000000000000 : ℝ)+2*(28790264691/90650000000000 : ℝ)*(9921/100000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (9064455821775532889/9065000000000000000 : ℝ)+2*(28790264691/90650000000000 : ℝ)*(9921/100000 : ℝ)=(5000014935580547/5000000000000000 : ℝ) by norm_num, show 1+2*(761806786703771/100000000000000000000 : ℝ)=(50000761806786703771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3127570750914099/25000000000000000000 : ℝ)+(761806786703771/100000000000000000000 : ℝ) ≤ ((9064455821775532889/9065000000000000000 : ℝ)+(28790264691/90650000000000 : ℝ)*((17173/100000 : ℝ)+(9921/100000 : ℝ)))^(5223/1024 : ℝ) := by
    rw [show (9064455821775532889/9065000000000000000 : ℝ)+(28790264691/90650000000000 : ℝ)*((17173/100000 : ℝ)+(9921/100000 : ℝ))=(5000130096639311/5000000000000000 : ℝ) by norm_num, show 1+(3127570750914099/25000000000000000000 : ℝ)+(761806786703771/100000000000000000000 : ℝ)=(100013272089790360167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3127570750914099/25000000000000000000 : ℝ) ≤ ((9064455821775532889/9065000000000000000 : ℝ)+2*(28790264691/90650000000000 : ℝ)*(17173/100000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (9064455821775532889/9065000000000000000 : ℝ)+2*(28790264691/90650000000000 : ℝ)*(17173/100000 : ℝ)=(200009810307923/200000000000000 : ℝ) by norm_num, show 1+2*(3127570750914099/25000000000000000000 : ℝ)=(12503127570750914099/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9064455821775532889/9065000000000000000 : ℝ)*(X 1 0+X 2 0)+(28790264691/90650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (9921/100000 : ℝ)) (hi := (17173/100000 : ℝ)) (c := (9064455821775532889/9065000000000000000 : ℝ)) (alpha := (28790264691/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9064455821775532889/9065000000000000000 : ℝ)*(X 0 1+X 2 1)+(28790264691/90650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (9921/100000 : ℝ)) (hi := (17173/100000 : ℝ)) (c := (9064455821775532889/9065000000000000000 : ℝ)) (alpha := (28790264691/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9064455821775532889/9065000000000000000 : ℝ)*(X 0 2+X 1 2)+(28790264691/90650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (9921/100000 : ℝ)) (hi := (17173/100000 : ℝ)) (c := (9064455821775532889/9065000000000000000 : ℝ)) (alpha := (28790264691/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-289053051/2000000000 : ℝ)*X 0 0+(2737930593/5000000000 : ℝ)*X 0 1+(256853863/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346539171/10000000000 : ℝ)*X 1 0+(-50658401/312500000 : ℝ)*X 1 1+(256853863/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346539171/10000000000 : ℝ)*X 2 0+(256853863/500000000 : ℝ)*X 2 1+(-50658401/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2058215971/5000000000 : ℝ)*X 0 0+(1826801719/5000000000 : ℝ)*X 0 1+(2307837803/5000000000 : ℝ)*X 0 2+(2058215971/5000000000 : ℝ)*X 1 0+(1826801719/5000000000 : ℝ)*X 1 1+(2307837803/5000000000 : ℝ)*X 1 2+(2058215971/5000000000 : ℝ)*X 2 0+(1826801719/5000000000 : ℝ)*X 2 1+(2307837803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1445420603/10000000000 : ℝ)*X 0 0+(2570399873/5000000000 : ℝ)*X 0 1+(2736041573/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5255888819/10000000000 : ℝ)*X 1 0+(-1286062949/10000000000 : ℝ)*X 1 1+(684010393/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051177763/2000000000 : ℝ)*X 2 0+(109441663/200000000 : ℝ)*X 2 1+(-643031473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4116873097/10000000000 : ℝ)*X 0 0+(4605104557/10000000000 : ℝ)*X 0 1+(458041531/1250000000 : ℝ)*X 0 2+(4116873097/10000000000 : ℝ)*X 1 0+(4605104557/10000000000 : ℝ)*X 1 1+(458041531/1250000000 : ℝ)*X 1 2+(4116873097/10000000000 : ℝ)*X 2 0+(4605104557/10000000000 : ℝ)*X 2 1+(458041531/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53910249345842101420149/4532500000000000000000000000 : ℝ) := by norm_num
    linear_combination (55583841/3125000000000 : ℝ)*(base19) + (41773281/2500000000000 : ℝ)*(base23) + (28804927/50000000000000 : ℝ)*(lower2) + (11575001/4000000000000 : ℝ)*(upper3) + (211923687/100000000000000 : ℝ)*(upper5) + (997801112186379/50000000000000 : ℝ)*(major0) + (997801112186379/50000000000000 : ℝ)*(major1) + (997801112186379/50000000000000 : ℝ)*(major2) + (2951751442940027/100000000000000 : ℝ)*(sp0) + (59035336911781/2000000000000 : ℝ)*(sp1) + (1475883476670361/50000000000000 : ℝ)*(sp2) + (1039428861225389/100000000000000 : ℝ)*(sp3) + (3436266387/20000000000000 : ℝ)*(sp4) + (656677639/10000000000000 : ℝ)*(sp7) + (1039435428001779/100000000000000 : ℝ)*(f.failure) + (1475884312135981/50000000000000 : ℝ)*(f.sum) + (2704826102007/4532500000000000000000000000 : ℝ)*base66 + (1511191181516781069/453250000000000000000000000000000 : ℝ)*base68 + (1550665839503218931/453250000000000000000000000000000 : ℝ)*base69 + (1385394215757281069/453250000000000000000000000000000 : ℝ)*base72 + (120328377941/141640625000000000000000000 : ℝ)*base74 + (431387867225718931/453250000000000000000000000000000 : ℝ)*base75 + (840632606128718931/453250000000000000000000000000000 : ℝ)*base77 + (1082145269977781069/453250000000000000000000000000000 : ℝ)*base80 + (9974515528403/4532500000000000000000000000 : ℝ)*base81 + (1130877/2500000000000000000000 : ℝ)*base89 + (1130877/2500000000000000000000 : ℝ)*base91 + (1130877/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52741234102834535768217/9065000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162294567/20000000000000 : ℝ)*(base19) + (872846063/100000000000000 : ℝ)*(base23) + (243041537/100000000000000 : ℝ)*(lower1) + (123782901/100000000000000 : ℝ)*(upper3) + (1135953/4000000000000 : ℝ)*(lower4) + (121537617/100000000000000 : ℝ)*(upper5) + (1020377453777069/50000000000000 : ℝ)*(major0) + (1020377453777069/50000000000000 : ℝ)*(major1) + (1020377453777069/50000000000000 : ℝ)*(major2) + (558814489/100000000000000 : ℝ)*(sp2) + (1509277914821121/50000000000000 : ℝ)*(sp4) + (47164922158897/1562500000000 : ℝ)*(sp5) + (301855439798169/10000000000000 : ℝ)*(sp6) + (16608652992637/1562500000000 : ℝ)*(sp7) + (16608652992637/1562500000000 : ℝ)*(f.failure) + (1509277914821121/50000000000000 : ℝ)*(f.sum) + (19511458392833/4532500000000000000000000000 : ℝ)*base65 + (4716779281250422341/453250000000000000000000000000000 : ℝ)*base67 + (4120597430185577659/453250000000000000000000000000000 : ℝ)*base70 + (47462692068104577659/453250000000000000000000000000000 : ℝ)*base72 + (2266930968439/2266250000000000000000000000 : ℝ)*base73 + (22973714936800577659/453250000000000000000000000000000 : ℝ)*base76 + (377121674590172341/453250000000000000000000000000000 : ℝ)*base77 + (1583247595049422341/453250000000000000000000000000000 : ℝ)*base79 + (1721847351139/566562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3719/39062500000000000000 : ℝ)*base90 + (3719/39062500000000000000 : ℝ)*base92 + (3719/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1701_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4967/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1701_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1701_s4_0 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-722636821/5000000000 : ℝ)*x 0 + (5475831167/10000000000 : ℝ)*x 1 + (5137101589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (722636821/5000000000 : ℝ)^5231 ≤ (4512827175133/50000000000000 : ℝ)^4207 := by
    have hnat : (722636821 : ℕ)^5231*50000000000000^4207 ≤ 4512827175133^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722636821 5000000000 4512827175133 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475831167/10000000000 : ℝ)^5231 ≤ (47292011244919/100000000000000 : ℝ)^4207 := by
    have hnat : (5475831167 : ℕ)^5231*100000000000000^4207 ≤ 47292011244919^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475831167 10000000000 47292011244919 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137101589/10000000000 : ℝ)^5231 ≤ (349458675071/800000000000 : ℝ)^4207 := by
    have hnat : (5137101589 : ℕ)^5231*800000000000^4207 ≤ 349458675071^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137101589 10000000000 349458675071 800000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-722636821/5000000000 : ℝ), (5475831167/10000000000 : ℝ), (5137101589/10000000000 : ℝ)] ![(4512827175133/50000000000000 : ℝ), (47292011244919/100000000000000 : ℝ), (349458675071/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-722636821/5000000000 : ℝ)|^5231 ≤ (4512827175133/50000000000000 : ℝ)^4207
        have hw : |(-722636821/5000000000 : ℝ)|=(722636821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475831167/10000000000 : ℝ)|^5231 ≤ (47292011244919/100000000000000 : ℝ)^4207
        have hw : |(5475831167/10000000000 : ℝ)|=(5475831167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137101589/10000000000 : ℝ)|^5231 ≤ (349458675071/800000000000 : ℝ)^4207
        have hw : |(5137101589/10000000000 : ℝ)|=(5137101589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s4_1 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673265161/5000000000 : ℝ)*x 0 + (-810523633/5000000000 : ℝ)*x 1 + (2568551241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673265161/5000000000 : ℝ)^5231 ≤ (45907508172363/100000000000000 : ℝ)^4207 := by
    have hnat : (2673265161 : ℕ)^5231*100000000000000^4207 ≤ 45907508172363^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673265161 5000000000 45907508172363 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (810523633/5000000000 : ℝ)^5231 ≤ (2082029596953/20000000000000 : ℝ)^4207 := by
    have hnat : (810523633 : ℕ)^5231*20000000000000^4207 ≤ 2082029596953^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810523633 5000000000 2082029596953 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568551241/5000000000 : ℝ)^5231 ≤ (27301464891/62500000000 : ℝ)^4207 := by
    have hnat : (2568551241 : ℕ)^5231*62500000000^4207 ≤ 27301464891^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568551241 5000000000 27301464891 62500000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673265161/5000000000 : ℝ), (-810523633/5000000000 : ℝ), (2568551241/5000000000 : ℝ)] ![(45907508172363/100000000000000 : ℝ), (2082029596953/20000000000000 : ℝ), (27301464891/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673265161/5000000000 : ℝ)|^5231 ≤ (45907508172363/100000000000000 : ℝ)^4207
        have hw : |(2673265161/5000000000 : ℝ)|=(2673265161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-810523633/5000000000 : ℝ)|^5231 ≤ (2082029596953/20000000000000 : ℝ)^4207
        have hw : |(-810523633/5000000000 : ℝ)|=(810523633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568551241/5000000000 : ℝ)|^5231 ≤ (27301464891/62500000000 : ℝ)^4207
        have hw : |(2568551241/5000000000 : ℝ)|=(2568551241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s4_2 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346531071/10000000000 : ℝ)*x 0 + (321068863/625000000 : ℝ)*x 1 + (-405261789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346531071/10000000000 : ℝ)^5231 ≤ (4590751616897/10000000000000 : ℝ)^4207 := by
    have hnat : (5346531071 : ℕ)^5231*10000000000000^4207 ≤ 4590751616897^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346531071 10000000000 4590751616897 10000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321068863/625000000 : ℝ)^5231 ≤ (4368233669937/10000000000000 : ℝ)^4207 := by
    have hnat : (321068863 : ℕ)^5231*10000000000000^4207 ≤ 4368233669937^4207*625000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321068863 625000000 4368233669937 10000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405261789/2500000000 : ℝ)^5231 ≤ (5205073553209/50000000000000 : ℝ)^4207 := by
    have hnat : (405261789 : ℕ)^5231*50000000000000^4207 ≤ 5205073553209^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405261789 2500000000 5205073553209 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346531071/10000000000 : ℝ), (321068863/625000000 : ℝ), (-405261789/2500000000 : ℝ)] ![(4590751616897/10000000000000 : ℝ), (4368233669937/10000000000000 : ℝ), (5205073553209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346531071/10000000000 : ℝ)|^5231 ≤ (4590751616897/10000000000000 : ℝ)^4207
        have hw : |(5346531071/10000000000 : ℝ)|=(5346531071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321068863/625000000 : ℝ)|^5231 ≤ (4368233669937/10000000000000 : ℝ)^4207
        have hw : |(321068863/625000000 : ℝ)|=(321068863/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405261789/2500000000 : ℝ)|^5231 ≤ (5205073553209/50000000000000 : ℝ)^4207
        have hw : |(-405261789/2500000000 : ℝ)|=(405261789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s4_3 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4116437419/10000000000 : ℝ)*x 0 + (3653680621/10000000000 : ℝ)*x 1 + (1153899341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116437419/10000000000 : ℝ)^5231 ≤ (33166112557869/100000000000000 : ℝ)^4207 := by
    have hnat : (4116437419 : ℕ)^5231*100000000000000^4207 ≤ 33166112557869^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116437419 10000000000 33166112557869 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3653680621/10000000000 : ℝ)^5231 ≤ (28595488595509/100000000000000 : ℝ)^4207 := by
    have hnat : (3653680621 : ℕ)^5231*100000000000000^4207 ≤ 28595488595509^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3653680621 10000000000 28595488595509 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153899341/2500000000 : ℝ)^5231 ≤ (38238398828223/100000000000000 : ℝ)^4207 := by
    have hnat : (1153899341 : ℕ)^5231*100000000000000^4207 ≤ 38238398828223^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153899341 2500000000 38238398828223 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116437419/10000000000 : ℝ), (3653680621/10000000000 : ℝ), (1153899341/2500000000 : ℝ)] ![(33166112557869/100000000000000 : ℝ), (28595488595509/100000000000000 : ℝ), (38238398828223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116437419/10000000000 : ℝ)|^5231 ≤ (33166112557869/100000000000000 : ℝ)^4207
        have hw : |(4116437419/10000000000 : ℝ)|=(4116437419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3653680621/10000000000 : ℝ)|^5231 ≤ (28595488595509/100000000000000 : ℝ)^4207
        have hw : |(3653680621/10000000000 : ℝ)|=(3653680621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1153899341/2500000000 : ℝ)|^5231 ≤ (38238398828223/100000000000000 : ℝ)^4207
        have hw : |(1153899341/2500000000 : ℝ)|=(1153899341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s4_4 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-57817153/400000000 : ℝ)*x 0 + (64260291/125000000 : ℝ)*x 1 + (2736027011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57817153/400000000 : ℝ)^5231 ≤ (112835742003/1250000000000 : ℝ)^4207 := by
    have hnat : (57817153 : ℕ)^5231*1250000000000^4207 ≤ 112835742003^4207*400000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57817153 400000000 112835742003 1250000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64260291/125000000 : ℝ)^5231 ≤ (43721687442087/100000000000000 : ℝ)^4207 := by
    have hnat : (64260291 : ℕ)^5231*100000000000000^4207 ≤ 43721687442087^4207*125000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64260291 125000000 43721687442087 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736027011/5000000000 : ℝ)^5231 ≤ (47251453188599/100000000000000 : ℝ)^4207 := by
    have hnat : (2736027011 : ℕ)^5231*100000000000000^4207 ≤ 47251453188599^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736027011 5000000000 47251453188599 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57817153/400000000 : ℝ), (64260291/125000000 : ℝ), (2736027011/5000000000 : ℝ)] ![(112835742003/1250000000000 : ℝ), (43721687442087/100000000000000 : ℝ), (47251453188599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57817153/400000000 : ℝ)|^5231 ≤ (112835742003/1250000000000 : ℝ)^4207
        have hw : |(-57817153/400000000 : ℝ)|=(57817153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64260291/125000000 : ℝ)|^5231 ≤ (43721687442087/100000000000000 : ℝ)^4207
        have hw : |(64260291/125000000 : ℝ)|=(64260291/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736027011/5000000000 : ℝ)|^5231 ≤ (47251453188599/100000000000000 : ℝ)^4207
        have hw : |(2736027011/5000000000 : ℝ)|=(2736027011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_s4_5 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4116878403/10000000000 : ℝ)*x 0 + (921005869/2000000000 : ℝ)*x 1 + (114512697/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116878403/10000000000 : ℝ)^5231 ≤ (33170530436243/100000000000000 : ℝ)^4207 := by
    have hnat : (4116878403 : ℕ)^5231*100000000000000^4207 ≤ 33170530436243^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116878403 10000000000 33170530436243 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921005869/2000000000 : ℝ)^5231 ≤ (38129566863057/100000000000000 : ℝ)^4207 := by
    have hnat : (921005869 : ℕ)^5231*100000000000000^4207 ≤ 38129566863057^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921005869 2000000000 38129566863057 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114512697/312500000 : ℝ)^5231 ≤ (896871959023/3125000000000 : ℝ)^4207 := by
    have hnat : (114512697 : ℕ)^5231*3125000000000^4207 ≤ 896871959023^4207*312500000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114512697 312500000 896871959023 3125000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116878403/10000000000 : ℝ), (921005869/2000000000 : ℝ), (114512697/312500000 : ℝ)] ![(33170530436243/100000000000000 : ℝ), (38129566863057/100000000000000 : ℝ), (896871959023/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116878403/10000000000 : ℝ)|^5231 ≤ (33170530436243/100000000000000 : ℝ)^4207
        have hw : |(4116878403/10000000000 : ℝ)|=(4116878403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921005869/2000000000 : ℝ)|^5231 ≤ (38129566863057/100000000000000 : ℝ)^4207
        have hw : |(921005869/2000000000 : ℝ)|=(921005869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114512697/312500000 : ℝ)|^5231 ≤ (896871959023/3125000000000 : ℝ)^4207
        have hw : |(114512697/312500000 : ℝ)|=(114512697/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1701_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4967/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1987/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17157/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4967/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4967/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4967/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4967/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4967/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4967/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4967/50000 : ℝ) ^ (5223/1024 : ℝ) ≤ (3834560335481/500000000000000000 : ℝ) := by
    have hpowers : (4967/50000 : ℝ)^5223 ≤ (3834560335481/500000000000000000 : ℝ)^1024 := by
      have hnat : (4967 : ℕ)^5223*500000000000000000^1024 ≤ 3834560335481^1024*50000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4967 50000 3834560335481 500000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4967/50000 : ℝ)) (X := (3834560335481/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17157/100000 : ℝ) ^ (5223/1024 : ℝ) ≤ (2490189041489691/20000000000000000000 : ℝ) := by
    have hpowers : (17157/100000 : ℝ)^5223 ≤ (2490189041489691/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17157 : ℕ)^5223*20000000000000000000^1024 ≤ 2490189041489691^1024*100000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17157 100000 2490189041489691 20000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17157/100000 : ℝ)) (X := (2490189041489691/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250003834560335481/250000000000000000 : ℝ) ≤ (10000030071342709/10000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (250003834560335481/250000000000000000 : ℝ)^1024 ≤ (10000030071342709/10000000000000000 : ℝ)^5223 := by
      have hnat : (250003834560335481 : ℕ)^1024*10000000000000000^5223 ≤ 10000030071342709^5223*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250003834560335481 250000000000000000 10000030071342709 10000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030071342709/10000000000000000 : ℝ)) (X := (250003834560335481/250000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002643571454908931/20000000000000000000 : ℝ) ≤ (10000259130131321/10000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (20002643571454908931/20000000000000000000 : ℝ)^1024 ≤ (10000259130131321/10000000000000000 : ℝ)^5223 := by
      have hnat : (20002643571454908931 : ℕ)^1024*10000000000000000^5223 ≤ 10000259130131321^5223*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002643571454908931 20000000000000000000 10000259130131321 10000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000259130131321/10000000000000000 : ℝ)) (X := (20002643571454908931/20000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002490189041489691/10000000000000000000 : ℝ) ≤ (10000488188919933/10000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (10002490189041489691/10000000000000000000 : ℝ)^1024 ≤ (10000488188919933/10000000000000000 : ℝ)^5223 := by
      have hnat : (10002490189041489691 : ℕ)^1024*10000000000000000^5223 ≤ 10000488188919933^5223*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002490189041489691 10000000000000000000 10000488188919933 10000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000488188919933/10000000000000000 : ℝ)) (X := (10002490189041489691/10000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3834560335481/500000000000000000 : ℝ) ≤ ((72225666265296243891/72230000000000000000 : ℝ)+2*(57264697153/180575000000000 : ℝ)*(4967/50000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (72225666265296243891/72230000000000000000 : ℝ)+2*(57264697153/180575000000000 : ℝ)*(4967/50000 : ℝ)=(10000030071342709/10000000000000000 : ℝ) by norm_num, show 1+2*(3834560335481/500000000000000000 : ℝ)=(250003834560335481/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2490189041489691/20000000000000000000 : ℝ)+(3834560335481/500000000000000000 : ℝ) ≤ ((72225666265296243891/72230000000000000000 : ℝ)+(57264697153/180575000000000 : ℝ)*((17157/100000 : ℝ)+(4967/50000 : ℝ)))^(5223/1024 : ℝ) := by
    rw [show (72225666265296243891/72230000000000000000 : ℝ)+(57264697153/180575000000000 : ℝ)*((17157/100000 : ℝ)+(4967/50000 : ℝ))=(10000259130131321/10000000000000000 : ℝ) by norm_num, show 1+(2490189041489691/20000000000000000000 : ℝ)+(3834560335481/500000000000000000 : ℝ)=(20002643571454908931/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2490189041489691/20000000000000000000 : ℝ) ≤ ((72225666265296243891/72230000000000000000 : ℝ)+2*(57264697153/180575000000000 : ℝ)*(17157/100000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (72225666265296243891/72230000000000000000 : ℝ)+2*(57264697153/180575000000000 : ℝ)*(17157/100000 : ℝ)=(10000488188919933/10000000000000000 : ℝ) by norm_num, show 1+2*(2490189041489691/20000000000000000000 : ℝ)=(10002490189041489691/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72225666265296243891/72230000000000000000 : ℝ)*(X 1 0+X 2 0)+(57264697153/180575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (4967/50000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (72225666265296243891/72230000000000000000 : ℝ)) (alpha := (57264697153/180575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72225666265296243891/72230000000000000000 : ℝ)*(X 0 1+X 2 1)+(57264697153/180575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (4967/50000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (72225666265296243891/72230000000000000000 : ℝ)) (alpha := (57264697153/180575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72225666265296243891/72230000000000000000 : ℝ)*(X 0 2+X 1 2)+(57264697153/180575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (4967/50000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (72225666265296243891/72230000000000000000 : ℝ)) (alpha := (57264697153/180575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-722636821/5000000000 : ℝ)*X 0 0+(5475831167/10000000000 : ℝ)*X 0 1+(5137101589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673265161/5000000000 : ℝ)*X 1 0+(-810523633/5000000000 : ℝ)*X 1 1+(2568551241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346531071/10000000000 : ℝ)*X 2 0+(321068863/625000000 : ℝ)*X 2 1+(-405261789/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4116437419/10000000000 : ℝ)*X 0 0+(3653680621/10000000000 : ℝ)*X 0 1+(1153899341/2500000000 : ℝ)*X 0 2+(4116437419/10000000000 : ℝ)*X 1 0+(3653680621/10000000000 : ℝ)*X 1 1+(1153899341/2500000000 : ℝ)*X 1 2+(4116437419/10000000000 : ℝ)*X 2 0+(3653680621/10000000000 : ℝ)*X 2 1+(1153899341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-57817153/400000000 : ℝ)*X 0 0+(64260291/125000000 : ℝ)*X 0 1+(2736027011/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4116878403/10000000000 : ℝ)*X 0 0+(921005869/2000000000 : ℝ)*X 0 1+(114512697/312500000 : ℝ)*X 0 2+(4116878403/10000000000 : ℝ)*X 1 0+(921005869/2000000000 : ℝ)*X 1 1+(114512697/312500000 : ℝ)*X 1 2+(4116878403/10000000000 : ℝ)*X 2 0+(921005869/2000000000 : ℝ)*X 2 1+(114512697/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11077906176481497473240760969/1805750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (447837197/50000000000000 : ℝ)*(base19) + (1281482811/100000000000000 : ℝ)*(base23) + (1856129/12500000000000 : ℝ)*(lower2) + (11689129/12500000000000 : ℝ)*(upper3) + (19626751/10000000000000 : ℝ)*(upper5) + (997960352864949/50000000000000 : ℝ)*(major0) + (997960352864949/50000000000000 : ℝ)*(major1) + (997960352864949/50000000000000 : ℝ)*(major2) + (295222181125333/10000000000000 : ℝ)*(sp0) + (2952238998124691/100000000000000 : ℝ)*(sp1) + (1476119306158137/50000000000000 : ℝ)*(sp2) + (8121844886297/781250000000 : ℝ)*(sp3) + (3616509151/20000000000000 : ℝ)*(sp4) + (5167721517/100000000000000 : ℝ)*(sp5) + (1039601313167533/100000000000000 : ℝ)*(f.failure) + (1476119946899543/50000000000000 : ℝ)*(f.sum) + (18548038430653/4514375000000000000000000000 : ℝ)*base66 + (21980751451641576559/3611500000000000000000000000000000 : ℝ)*base67 + (11530593923190076559/3611500000000000000000000000000000 : ℝ)*base69 + (16220171509962576559/3611500000000000000000000000000000 : ℝ)*base71 + (36090969160349/36115000000000000000000000000 : ℝ)*base74 + (21605721579547076559/3611500000000000000000000000000000 : ℝ)*base75 + (13867030239814576559/3611500000000000000000000000000000 : ℝ)*base77 + (30946260901298576559/3611500000000000000000000000000000 : ℝ)*base79 + (3139259896171/564296875000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5537821/2500000000000000000000 : ℝ)*base90 + (5537821/2500000000000000000000 : ℝ)*base92 + (5537821/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1701_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4967/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1987/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1701_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1701_box_0 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-559756961/5000000000 : ℝ)*x 0 + (2711019289/5000000000 : ℝ)*x 1 + (5422038587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559756961/5000000000 : ℝ)^5231 ≤ (6569912972807/100000000000000 : ℝ)^4207 := by
    have hnat : (559756961 : ℕ)^5231*100000000000000^4207 ≤ 6569912972807^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559756961 5000000000 6569912972807 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711019289/5000000000 : ℝ)^5231 ≤ (11678760865803/25000000000000 : ℝ)^4207 := by
    have hnat : (2711019289 : ℕ)^5231*25000000000000^4207 ≤ 11678760865803^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711019289 5000000000 11678760865803 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422038587/10000000000 : ℝ)^5231 ≤ (11678760889907/25000000000000 : ℝ)^4207 := by
    have hnat : (5422038587 : ℕ)^5231*25000000000000^4207 ≤ 11678760889907^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422038587 10000000000 11678760889907 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-559756961/5000000000 : ℝ), (2711019289/5000000000 : ℝ), (5422038587/10000000000 : ℝ)] ![(6569912972807/100000000000000 : ℝ), (11678760865803/25000000000000 : ℝ), (11678760889907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-559756961/5000000000 : ℝ)|^5231 ≤ (6569912972807/100000000000000 : ℝ)^4207
        have hw : |(-559756961/5000000000 : ℝ)|=(559756961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711019289/5000000000 : ℝ)|^5231 ≤ (11678760865803/25000000000000 : ℝ)^4207
        have hw : |(2711019289/5000000000 : ℝ)|=(2711019289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422038587/10000000000 : ℝ)|^5231 ≤ (11678760889907/25000000000000 : ℝ)^4207
        have hw : |(5422038587/10000000000 : ℝ)|=(5422038587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_1 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612886899/5000000000 : ℝ)*x 0 + (-21849993/156250000 : ℝ)*x 1 + (84719353/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612886899/5000000000 : ℝ)^5231 ≤ (5577728777157/12500000000000 : ℝ)^4207 := by
    have hnat : (2612886899 : ℕ)^5231*12500000000000^4207 ≤ 5577728777157^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612886899 5000000000 5577728777157 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21849993/156250000 : ℝ)^5231 ≤ (8663126156301/100000000000000 : ℝ)^4207 := by
    have hnat : (21849993 : ℕ)^5231*100000000000000^4207 ≤ 8663126156301^4207*156250000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21849993 156250000 8663126156301 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84719353/156250000 : ℝ)^5231 ≤ (5839380451649/12500000000000 : ℝ)^4207 := by
    have hnat : (84719353 : ℕ)^5231*12500000000000^4207 ≤ 5839380451649^4207*156250000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84719353 156250000 5839380451649 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612886899/5000000000 : ℝ), (-21849993/156250000 : ℝ), (84719353/156250000 : ℝ)] ![(5577728777157/12500000000000 : ℝ), (8663126156301/100000000000000 : ℝ), (5839380451649/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612886899/5000000000 : ℝ)|^5231 ≤ (5577728777157/12500000000000 : ℝ)^4207
        have hw : |(2612886899/5000000000 : ℝ)|=(2612886899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21849993/156250000 : ℝ)|^5231 ≤ (8663126156301/100000000000000 : ℝ)^4207
        have hw : |(-21849993/156250000 : ℝ)|=(21849993/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84719353/156250000 : ℝ)|^5231 ≤ (5839380451649/12500000000000 : ℝ)^4207
        have hw : |(84719353/156250000 : ℝ)|=(84719353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_2 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225773807/10000000000 : ℝ)*x 0 + (5422038587/10000000000 : ℝ)*x 1 + (-1398399547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225773807/10000000000 : ℝ)^5231 ≤ (44621830312811/100000000000000 : ℝ)^4207 := by
    have hnat : (5225773807 : ℕ)^5231*100000000000000^4207 ≤ 44621830312811^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225773807 10000000000 44621830312811 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422038587/10000000000 : ℝ)^5231 ≤ (11678760889907/25000000000000 : ℝ)^4207 := by
    have hnat : (5422038587 : ℕ)^5231*25000000000000^4207 ≤ 11678760889907^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422038587 10000000000 11678760889907 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1398399547/10000000000 : ℝ)^5231 ≤ (8663126117787/100000000000000 : ℝ)^4207 := by
    have hnat : (1398399547 : ℕ)^5231*100000000000000^4207 ≤ 8663126117787^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398399547 10000000000 8663126117787 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225773807/10000000000 : ℝ), (5422038587/10000000000 : ℝ), (-1398399547/10000000000 : ℝ)] ![(44621830312811/100000000000000 : ℝ), (11678760889907/25000000000000 : ℝ), (8663126117787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225773807/10000000000 : ℝ)|^5231 ≤ (44621830312811/100000000000000 : ℝ)^4207
        have hw : |(5225773807/10000000000 : ℝ)|=(5225773807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422038587/10000000000 : ℝ)|^5231 ≤ (11678760889907/25000000000000 : ℝ)^4207
        have hw : |(5422038587/10000000000 : ℝ)|=(5422038587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1398399547/10000000000 : ℝ)|^5231 ≤ (8663126117787/100000000000000 : ℝ)^4207
        have hw : |(-1398399547/10000000000 : ℝ)|=(1398399547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_3 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44993183/100000000 : ℝ)*x 0 + (1973529707/5000000000 : ℝ)*x 1 + (1973529713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44993183/100000000 : ℝ)^5231 ≤ (740885830921/2000000000000 : ℝ)^4207 := by
    have hnat : (44993183 : ℕ)^5231*2000000000000^4207 ≤ 740885830921^4207*100000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44993183 100000000 740885830921 2000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973529707/5000000000 : ℝ)^5231 ≤ (31477854157509/100000000000000 : ℝ)^4207 := by
    have hnat : (1973529707 : ℕ)^5231*100000000000000^4207 ≤ 31477854157509^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973529707 5000000000 31477854157509 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973529713/5000000000 : ℝ)^5231 ≤ (31477854276503/100000000000000 : ℝ)^4207 := by
    have hnat : (1973529713 : ℕ)^5231*100000000000000^4207 ≤ 31477854276503^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973529713 5000000000 31477854276503 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44993183/100000000 : ℝ), (1973529707/5000000000 : ℝ), (1973529713/5000000000 : ℝ)] ![(740885830921/2000000000000 : ℝ), (31477854157509/100000000000000 : ℝ), (31477854276503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44993183/100000000 : ℝ)|^5231 ≤ (740885830921/2000000000000 : ℝ)^4207
        have hw : |(44993183/100000000 : ℝ)|=(44993183/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1973529707/5000000000 : ℝ)|^5231 ≤ (31477854157509/100000000000000 : ℝ)^4207
        have hw : |(1973529707/5000000000 : ℝ)|=(1973529707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1973529713/5000000000 : ℝ)|^5231 ≤ (31477854276503/100000000000000 : ℝ)^4207
        have hw : |(1973529713/5000000000 : ℝ)|=(1973529713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_4 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-895904239/5000000000 : ℝ)*x 0 + (32356289/62500000 : ℝ)*x 1 + (2588503123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895904239/5000000000 : ℝ)^5231 ≤ (117907079999/1000000000000 : ℝ)^4207 := by
    have hnat : (895904239 : ℕ)^5231*1000000000000^4207 ≤ 117907079999^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895904239 5000000000 117907079999 1000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32356289/62500000 : ℝ)^5231 ≤ (44104645958671/100000000000000 : ℝ)^4207 := by
    have hnat : (32356289 : ℕ)^5231*100000000000000^4207 ≤ 44104645958671^4207*62500000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32356289 62500000 44104645958671 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588503123/5000000000 : ℝ)^5231 ≤ (11026161505557/25000000000000 : ℝ)^4207 := by
    have hnat : (2588503123 : ℕ)^5231*25000000000000^4207 ≤ 11026161505557^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588503123 5000000000 11026161505557 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-895904239/5000000000 : ℝ), (32356289/62500000 : ℝ), (2588503123/5000000000 : ℝ)] ![(117907079999/1000000000000 : ℝ), (44104645958671/100000000000000 : ℝ), (11026161505557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-895904239/5000000000 : ℝ)|^5231 ≤ (117907079999/1000000000000 : ℝ)^4207
        have hw : |(-895904239/5000000000 : ℝ)|=(895904239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32356289/62500000 : ℝ)|^5231 ≤ (44104645958671/100000000000000 : ℝ)^4207
        have hw : |(32356289/62500000 : ℝ)|=(32356289/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588503123/5000000000 : ℝ)|^5231 ≤ (11026161505557/25000000000000 : ℝ)^4207
        have hw : |(2588503123/5000000000 : ℝ)|=(2588503123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_5 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392311359/10000000000 : ℝ)*x 0 + (-752935103/5000000000 : ℝ)*x 1 + (2588503119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392311359/10000000000 : ℝ)^5231 ≤ (46396792034081/100000000000000 : ℝ)^4207 := by
    have hnat : (5392311359 : ℕ)^5231*100000000000000^4207 ≤ 46396792034081^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392311359 10000000000 46396792034081 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (752935103/5000000000 : ℝ)^5231 ≤ (1899712400967/20000000000000 : ℝ)^4207 := by
    have hnat : (752935103 : ℕ)^5231*20000000000000^4207 ≤ 1899712400967^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752935103 5000000000 1899712400967 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588503119/5000000000 : ℝ)^5231 ≤ (8820929187497/20000000000000 : ℝ)^4207 := by
    have hnat : (2588503119 : ℕ)^5231*20000000000000^4207 ≤ 8820929187497^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588503119 5000000000 8820929187497 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392311359/10000000000 : ℝ), (-752935103/5000000000 : ℝ), (2588503119/5000000000 : ℝ)] ![(46396792034081/100000000000000 : ℝ), (1899712400967/20000000000000 : ℝ), (8820929187497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392311359/10000000000 : ℝ)|^5231 ≤ (46396792034081/100000000000000 : ℝ)^4207
        have hw : |(5392311359/10000000000 : ℝ)|=(5392311359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-752935103/5000000000 : ℝ)|^5231 ≤ (1899712400967/20000000000000 : ℝ)^4207
        have hw : |(-752935103/5000000000 : ℝ)|=(752935103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588503119/5000000000 : ℝ)|^5231 ≤ (8820929187497/20000000000000 : ℝ)^4207
        have hw : |(2588503119/5000000000 : ℝ)|=(2588503119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_6 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696155679/5000000000 : ℝ)*x 0 + (2588503121/5000000000 : ℝ)*x 1 + (-1505870203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696155679/5000000000 : ℝ)^5231 ≤ (46396792023383/100000000000000 : ℝ)^4207 := by
    have hnat : (2696155679 : ℕ)^5231*100000000000000^4207 ≤ 46396792023383^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696155679 5000000000 46396792023383 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588503121/5000000000 : ℝ)^5231 ≤ (2756540373741/6250000000000 : ℝ)^4207 := by
    have hnat : (2588503121 : ℕ)^5231*6250000000000^4207 ≤ 2756540373741^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588503121 5000000000 2756540373741 6250000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1505870203/10000000000 : ℝ)^5231 ≤ (4749280990653/50000000000000 : ℝ)^4207 := by
    have hnat : (1505870203 : ℕ)^5231*50000000000000^4207 ≤ 4749280990653^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505870203 10000000000 4749280990653 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696155679/5000000000 : ℝ), (2588503121/5000000000 : ℝ), (-1505870203/10000000000 : ℝ)] ![(46396792023383/100000000000000 : ℝ), (2756540373741/6250000000000 : ℝ), (4749280990653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696155679/5000000000 : ℝ)|^5231 ≤ (46396792023383/100000000000000 : ℝ)^4207
        have hw : |(2696155679/5000000000 : ℝ)|=(2696155679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588503121/5000000000 : ℝ)|^5231 ≤ (2756540373741/6250000000000 : ℝ)^4207
        have hw : |(2588503121/5000000000 : ℝ)|=(2588503121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1505870203/10000000000 : ℝ)|^5231 ≤ (4749280990653/50000000000000 : ℝ)^4207
        have hw : |(-1505870203/10000000000 : ℝ)|=(1505870203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_7 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3718380401/10000000000 : ℝ)*x 0 + (433668651/1000000000 : ℝ)*x 1 + (542085813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3718380401/10000000000 : ℝ)^5231 ≤ (29226464476473/100000000000000 : ℝ)^4207 := by
    have hnat : (3718380401 : ℕ)^5231*100000000000000^4207 ≤ 29226464476473^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718380401 10000000000 29226464476473 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433668651/1000000000 : ℝ)^5231 ≤ (35386767782153/100000000000000 : ℝ)^4207 := by
    have hnat : (433668651 : ℕ)^5231*100000000000000^4207 ≤ 35386767782153^4207*1000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433668651 1000000000 35386767782153 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542085813/1250000000 : ℝ)^5231 ≤ (35386767721277/100000000000000 : ℝ)^4207 := by
    have hnat : (542085813 : ℕ)^5231*100000000000000^4207 ≤ 35386767721277^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542085813 1250000000 35386767721277 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3718380401/10000000000 : ℝ), (433668651/1000000000 : ℝ), (542085813/1250000000 : ℝ)] ![(29226464476473/100000000000000 : ℝ), (35386767782153/100000000000000 : ℝ), (35386767721277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3718380401/10000000000 : ℝ)|^5231 ≤ (29226464476473/100000000000000 : ℝ)^4207
        have hw : |(3718380401/10000000000 : ℝ)|=(3718380401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(433668651/1000000000 : ℝ)|^5231 ≤ (35386767782153/100000000000000 : ℝ)^4207
        have hw : |(433668651/1000000000 : ℝ)|=(433668651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542085813/1250000000 : ℝ)|^5231 ≤ (35386767721277/100000000000000 : ℝ)^4207
        have hw : |(542085813/1250000000 : ℝ)|=(542085813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_8 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-823677189/5000000000 : ℝ)*x 0 + (624577423/1250000000 : ℝ)*x 1 + (1366288709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823677189/5000000000 : ℝ)^5231 ≤ (10620622747779/100000000000000 : ℝ)^4207 := by
    have hnat : (823677189 : ℕ)^5231*100000000000000^4207 ≤ 10620622747779^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823677189 5000000000 10620622747779 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624577423/1250000000 : ℝ)^5231 ≤ (42201988215169/100000000000000 : ℝ)^4207 := by
    have hnat : (624577423 : ℕ)^5231*100000000000000^4207 ≤ 42201988215169^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624577423 1250000000 42201988215169 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366288709/2500000000 : ℝ)^5231 ≤ (47177389013633/100000000000000 : ℝ)^4207 := by
    have hnat : (1366288709 : ℕ)^5231*100000000000000^4207 ≤ 47177389013633^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366288709 2500000000 47177389013633 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-823677189/5000000000 : ℝ), (624577423/1250000000 : ℝ), (1366288709/2500000000 : ℝ)] ![(10620622747779/100000000000000 : ℝ), (42201988215169/100000000000000 : ℝ), (47177389013633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-823677189/5000000000 : ℝ)|^5231 ≤ (10620622747779/100000000000000 : ℝ)^4207
        have hw : |(-823677189/5000000000 : ℝ)|=(823677189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624577423/1250000000 : ℝ)|^5231 ≤ (42201988215169/100000000000000 : ℝ)^4207
        have hw : |(624577423/1250000000 : ℝ)|=(624577423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366288709/2500000000 : ℝ)|^5231 ≤ (47177389013633/100000000000000 : ℝ)^4207
        have hw : |(1366288709/2500000000 : ℝ)|=(1366288709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_9 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196485291/10000000000 : ℝ)*x 0 + (-137868501/1000000000 : ℝ)*x 1 + (2732577489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196485291/10000000000 : ℝ)^5231 ≤ (2215554070743/5000000000000 : ℝ)^4207 := by
    have hnat : (5196485291 : ℕ)^5231*5000000000000^4207 ≤ 2215554070743^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196485291 10000000000 2215554070743 5000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137868501/1000000000 : ℝ)^5231 ≤ (2127882009241/25000000000000 : ℝ)^4207 := by
    have hnat : (137868501 : ℕ)^5231*25000000000000^4207 ≤ 2127882009241^4207*1000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137868501 1000000000 2127882009241 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732577489/5000000000 : ℝ)^5231 ≤ (23588695268899/50000000000000 : ℝ)^4207 := by
    have hnat : (2732577489 : ℕ)^5231*50000000000000^4207 ≤ 23588695268899^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732577489 5000000000 23588695268899 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196485291/10000000000 : ℝ), (-137868501/1000000000 : ℝ), (2732577489/5000000000 : ℝ)] ![(2215554070743/5000000000000 : ℝ), (2127882009241/25000000000000 : ℝ), (23588695268899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196485291/10000000000 : ℝ)|^5231 ≤ (2215554070743/5000000000000 : ℝ)^4207
        have hw : |(5196485291/10000000000 : ℝ)|=(5196485291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137868501/1000000000 : ℝ)|^5231 ≤ (2127882009241/25000000000000 : ℝ)^4207
        have hw : |(-137868501/1000000000 : ℝ)|=(137868501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732577489/5000000000 : ℝ)|^5231 ≤ (23588695268899/50000000000000 : ℝ)^4207
        have hw : |(2732577489/5000000000 : ℝ)|=(2732577489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_10 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519648539/1000000000 : ℝ)*x 0 + (5465155003/10000000000 : ℝ)*x 1 + (-1378684837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519648539/1000000000 : ℝ)^5231 ≤ (44311082464523/100000000000000 : ℝ)^4207 := by
    have hnat : (519648539 : ℕ)^5231*100000000000000^4207 ≤ 44311082464523^4207*1000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519648539 1000000000 44311082464523 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465155003/10000000000 : ℝ)^5231 ≤ (47177390806137/100000000000000 : ℝ)^4207 := by
    have hnat : (5465155003 : ℕ)^5231*100000000000000^4207 ≤ 47177390806137^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465155003 10000000000 47177390806137 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378684837/10000000000 : ℝ)^5231 ≤ (1702305341791/20000000000000 : ℝ)^4207 := by
    have hnat : (1378684837 : ℕ)^5231*20000000000000^4207 ≤ 1702305341791^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378684837 10000000000 1702305341791 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519648539/1000000000 : ℝ), (5465155003/10000000000 : ℝ), (-1378684837/10000000000 : ℝ)] ![(44311082464523/100000000000000 : ℝ), (47177390806137/100000000000000 : ℝ), (1702305341791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519648539/1000000000 : ℝ)|^5231 ≤ (44311082464523/100000000000000 : ℝ)^4207
        have hw : |(519648539/1000000000 : ℝ)|=(519648539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465155003/10000000000 : ℝ)|^5231 ≤ (47177390806137/100000000000000 : ℝ)^4207
        have hw : |(5465155003/10000000000 : ℝ)|=(5465155003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1378684837/10000000000 : ℝ)|^5231 ≤ (1702305341791/20000000000000 : ℝ)^4207
        have hw : |(-1378684837/10000000000 : ℝ)|=(1378684837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_11 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1157932357/2500000000 : ℝ)*x 0 + (775664023/2000000000 : ℝ)*x 1 + (1939160163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1157932357/2500000000 : ℝ)^5231 ≤ (38404647604471/100000000000000 : ℝ)^4207 := by
    have hnat : (1157932357 : ℕ)^5231*100000000000000^4207 ≤ 38404647604471^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157932357 2500000000 38404647604471 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775664023/2000000000 : ℝ)^5231 ≤ (3849709393589/12500000000000 : ℝ)^4207 := by
    have hnat : (775664023 : ℕ)^5231*12500000000000^4207 ≤ 3849709393589^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775664023 2000000000 3849709393589 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939160163/5000000000 : ℝ)^5231 ≤ (15398838616047/50000000000000 : ℝ)^4207 := by
    have hnat : (1939160163 : ℕ)^5231*50000000000000^4207 ≤ 15398838616047^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939160163 5000000000 15398838616047 50000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1157932357/2500000000 : ℝ), (775664023/2000000000 : ℝ), (1939160163/5000000000 : ℝ)] ![(38404647604471/100000000000000 : ℝ), (3849709393589/12500000000000 : ℝ), (15398838616047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1157932357/2500000000 : ℝ)|^5231 ≤ (38404647604471/100000000000000 : ℝ)^4207
        have hw : |(1157932357/2500000000 : ℝ)|=(1157932357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(775664023/2000000000 : ℝ)|^5231 ≤ (3849709393589/12500000000000 : ℝ)^4207
        have hw : |(775664023/2000000000 : ℝ)|=(775664023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1939160163/5000000000 : ℝ)|^5231 ≤ (15398838616047/50000000000000 : ℝ)^4207
        have hw : |(1939160163/5000000000 : ℝ)|=(1939160163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_12 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15734837/125000000 : ℝ)*x 0 + (1118741769/2000000000 : ℝ)*x 1 + (5151793837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15734837/125000000 : ℝ)^5231 ≤ (1520222441307/20000000000000 : ℝ)^4207 := by
    have hnat : (15734837 : ℕ)^5231*20000000000000^4207 ≤ 1520222441307^4207*125000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15734837 125000000 1520222441307 20000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118741769/2000000000 : ℝ)^5231 ≤ (12140289407403/25000000000000 : ℝ)^4207 := by
    have hnat : (1118741769 : ℕ)^5231*25000000000000^4207 ≤ 12140289407403^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118741769 2000000000 12140289407403 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151793837/10000000000 : ℝ)^5231 ≤ (10959432536729/25000000000000 : ℝ)^4207 := by
    have hnat : (5151793837 : ℕ)^5231*25000000000000^4207 ≤ 10959432536729^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151793837 10000000000 10959432536729 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15734837/125000000 : ℝ), (1118741769/2000000000 : ℝ), (5151793837/10000000000 : ℝ)] ![(1520222441307/20000000000000 : ℝ), (12140289407403/25000000000000 : ℝ), (10959432536729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15734837/125000000 : ℝ)|^5231 ≤ (1520222441307/20000000000000 : ℝ)^4207
        have hw : |(-15734837/125000000 : ℝ)|=(15734837/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118741769/2000000000 : ℝ)|^5231 ≤ (12140289407403/25000000000000 : ℝ)^4207
        have hw : |(1118741769/2000000000 : ℝ)|=(1118741769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151793837/10000000000 : ℝ)|^5231 ≤ (10959432536729/25000000000000 : ℝ)^4207
        have hw : |(5151793837/10000000000 : ℝ)|=(5151793837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_13 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1352369097/2500000000 : ℝ)*x 0 + (-758234867/5000000000 : ℝ)*x 1 + (2575896939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352369097/2500000000 : ℝ)^5231 ≤ (46580504160181/100000000000000 : ℝ)^4207 := by
    have hnat : (1352369097 : ℕ)^5231*100000000000000^4207 ≤ 46580504160181^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352369097 2500000000 46580504160181 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758234867/5000000000 : ℝ)^5231 ≤ (9581765251093/100000000000000 : ℝ)^4207 := by
    have hnat : (758234867 : ℕ)^5231*100000000000000^4207 ≤ 9581765251093^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758234867 5000000000 9581765251093 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575896939/5000000000 : ℝ)^5231 ≤ (5479716322589/12500000000000 : ℝ)^4207 := by
    have hnat : (2575896939 : ℕ)^5231*12500000000000^4207 ≤ 5479716322589^4207*5000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575896939 5000000000 5479716322589 12500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352369097/2500000000 : ℝ), (-758234867/5000000000 : ℝ), (2575896939/5000000000 : ℝ)] ![(46580504160181/100000000000000 : ℝ), (9581765251093/100000000000000 : ℝ), (5479716322589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352369097/2500000000 : ℝ)|^5231 ≤ (46580504160181/100000000000000 : ℝ)^4207
        have hw : |(1352369097/2500000000 : ℝ)|=(1352369097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-758234867/5000000000 : ℝ)|^5231 ≤ (9581765251093/100000000000000 : ℝ)^4207
        have hw : |(-758234867/5000000000 : ℝ)|=(758234867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575896939/5000000000 : ℝ)|^5231 ≤ (5479716322589/12500000000000 : ℝ)^4207
        have hw : |(2575896939/5000000000 : ℝ)|=(2575896939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_14 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1352369123/2500000000 : ℝ)*x 0 + (1030358759/2000000000 : ℝ)*x 1 + (-189558713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352369123/2500000000 : ℝ)^5231 ≤ (11645126318423/25000000000000 : ℝ)^4207 := by
    have hnat : (1352369123 : ℕ)^5231*25000000000000^4207 ≤ 11645126318423^4207*2500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352369123 2500000000 11645126318423 25000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030358759/2000000000 : ℝ)^5231 ≤ (43837729702539/100000000000000 : ℝ)^4207 := by
    have hnat : (1030358759 : ℕ)^5231*100000000000000^4207 ≤ 43837729702539^4207*2000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030358759 2000000000 43837729702539 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189558713/1250000000 : ℝ)^5231 ≤ (47908825077/500000000000 : ℝ)^4207 := by
    have hnat : (189558713 : ℕ)^5231*500000000000^4207 ≤ 47908825077^4207*1250000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189558713 1250000000 47908825077 500000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352369123/2500000000 : ℝ), (1030358759/2000000000 : ℝ), (-189558713/1250000000 : ℝ)] ![(11645126318423/25000000000000 : ℝ), (43837729702539/100000000000000 : ℝ), (47908825077/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352369123/2500000000 : ℝ)|^5231 ≤ (11645126318423/25000000000000 : ℝ)^4207
        have hw : |(1352369123/2500000000 : ℝ)|=(1352369123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030358759/2000000000 : ℝ)|^5231 ≤ (43837729702539/100000000000000 : ℝ)^4207
        have hw : |(1030358759/2000000000 : ℝ)|=(1030358759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189558713/1250000000 : ℝ)|^5231 ≤ (47908825077/500000000000 : ℝ)^4207
        have hw : |(-189558713/1250000000 : ℝ)|=(189558713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1701_box_15 (p : ℝ) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (181752141/500000000 : ℝ)*x 0 + (4376669309/10000000000 : ℝ)*x 1 + (4376669011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181752141/500000000 : ℝ)^5231 ≤ (1775889240401/6250000000000 : ℝ)^4207 := by
    have hnat : (181752141 : ℕ)^5231*6250000000000^4207 ≤ 1775889240401^4207*500000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181752141 500000000 1775889240401 6250000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4376669309/10000000000 : ℝ)^5231 ≤ (35792887587081/100000000000000 : ℝ)^4207 := by
    have hnat : (4376669309 : ℕ)^5231*100000000000000^4207 ≤ 35792887587081^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376669309 10000000000 35792887587081 100000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4376669011/10000000000 : ℝ)^5231 ≤ (3579288455681/10000000000000 : ℝ)^4207 := by
    have hnat : (4376669011 : ℕ)^5231*10000000000000^4207 ≤ 3579288455681^4207*10000000000^5231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376669011 10000000000 3579288455681 10000000000000 5231 4207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5231/1024 : ℝ)) 5231 4207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181752141/500000000 : ℝ), (4376669309/10000000000 : ℝ), (4376669011/10000000000 : ℝ)] ![(1775889240401/6250000000000 : ℝ), (35792887587081/100000000000000 : ℝ), (3579288455681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181752141/500000000 : ℝ)|^5231 ≤ (1775889240401/6250000000000 : ℝ)^4207
        have hw : |(181752141/500000000 : ℝ)|=(181752141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4376669309/10000000000 : ℝ)|^5231 ≤ (35792887587081/100000000000000 : ℝ)^4207
        have hw : |(4376669309/10000000000 : ℝ)|=(4376669309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4376669011/10000000000 : ℝ)|^5231 ≤ (3579288455681/10000000000000 : ℝ)^4207
        have hw : |(4376669011/10000000000 : ℝ)|=(4376669011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1701_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1987/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13333/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58191/100000 : ℝ) ∧ (2537/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45147/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1987/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1987/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1987/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1987/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1987/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1987/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1987/20000 : ℝ) ^ (5223/1024 : ℝ) ≤ (383652958670431/50000000000000000000 : ℝ) := by
    have hpowers : (1987/20000 : ℝ)^5223 ≤ (383652958670431/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1987 : ℕ)^5223*50000000000000000000^1024 ≤ 383652958670431^1024*20000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1987 20000 383652958670431 50000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1987/20000 : ℝ)) (X := (383652958670431/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17157/100000 : ℝ) ^ (5223/1024 : ℝ) ≤ (2490189041489691/20000000000000000000 : ℝ) := by
    have hpowers : (17157/100000 : ℝ)^5223 ≤ (2490189041489691/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17157 : ℕ)^5223*20000000000000000000^1024 ≤ 2490189041489691^1024*100000^5223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17157 100000 2490189041489691 20000000000000000000 5223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17157/100000 : ℝ)) (X := (2490189041489691/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000383652958670431/25000000000000000000 : ℝ) ≤ (2500007521696463/2500000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (25000383652958670431/25000000000000000000 : ℝ)^1024 ≤ (2500007521696463/2500000000000000 : ℝ)^5223 := by
      have hnat : (25000383652958670431 : ℕ)^1024*2500000000000000^5223 ≤ 2500007521696463^5223*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000383652958670431 25000000000000000000 2500007521696463 2500000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500007521696463/2500000000000000 : ℝ)) (X := (25000383652958670431/25000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013218251124789317/100000000000000000000 : ℝ) ≤ (10000259137852167/10000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (100013218251124789317/100000000000000000000 : ℝ)^1024 ≤ (10000259137852167/10000000000000000 : ℝ)^5223 := by
      have hnat : (100013218251124789317 : ℕ)^1024*10000000000000000^5223 ≤ 10000259137852167^5223*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013218251124789317 100000000000000000000 10000259137852167 10000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000259137852167/10000000000000000 : ℝ)) (X := (100013218251124789317/100000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002490189041489691/10000000000000000000 : ℝ) ≤ (5000244094459241/5000000000000000 : ℝ) ^ (5223/1024 : ℝ) := by
    have hpowers : (10002490189041489691/10000000000000000000 : ℝ)^1024 ≤ (5000244094459241/5000000000000000 : ℝ)^5223 := by
      have hnat : (10002490189041489691 : ℕ)^1024*5000000000000000^5223 ≤ 5000244094459241^5223*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002490189041489691 10000000000000000000 5000244094459241 5000000000000000 1024 5223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000244094459241/5000000000000000 : ℝ)) (X := (10002490189041489691/10000000000000000000 : ℝ)) (by norm_num) 5223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(383652958670431/50000000000000000000 : ℝ) ≤ ((36107833021039872047/36110000000000000000 : ℝ)+2*(45810213263/144440000000000 : ℝ)*(1987/20000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (36107833021039872047/36110000000000000000 : ℝ)+2*(45810213263/144440000000000 : ℝ)*(1987/20000 : ℝ)=(2500007521696463/2500000000000000 : ℝ) by norm_num, show 1+2*(383652958670431/50000000000000000000 : ℝ)=(25000383652958670431/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2490189041489691/20000000000000000000 : ℝ)+(383652958670431/50000000000000000000 : ℝ) ≤ ((36107833021039872047/36110000000000000000 : ℝ)+(45810213263/144440000000000 : ℝ)*((17157/100000 : ℝ)+(1987/20000 : ℝ)))^(5223/1024 : ℝ) := by
    rw [show (36107833021039872047/36110000000000000000 : ℝ)+(45810213263/144440000000000 : ℝ)*((17157/100000 : ℝ)+(1987/20000 : ℝ))=(10000259137852167/10000000000000000 : ℝ) by norm_num, show 1+(2490189041489691/20000000000000000000 : ℝ)+(383652958670431/50000000000000000000 : ℝ)=(100013218251124789317/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2490189041489691/20000000000000000000 : ℝ) ≤ ((36107833021039872047/36110000000000000000 : ℝ)+2*(45810213263/144440000000000 : ℝ)*(17157/100000 : ℝ))^(5223/1024 : ℝ) := by
    rw [show (36107833021039872047/36110000000000000000 : ℝ)+2*(45810213263/144440000000000 : ℝ)*(17157/100000 : ℝ)=(5000244094459241/5000000000000000 : ℝ) by norm_num, show 1+2*(2490189041489691/20000000000000000000 : ℝ)=(10002490189041489691/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36107833021039872047/36110000000000000000 : ℝ)*(X 1 0+X 2 0)+(45810213263/144440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (1987/20000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (36107833021039872047/36110000000000000000 : ℝ)) (alpha := (45810213263/144440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36107833021039872047/36110000000000000000 : ℝ)*(X 0 1+X 2 1)+(45810213263/144440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (1987/20000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (36107833021039872047/36110000000000000000 : ℝ)) (alpha := (45810213263/144440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36107833021039872047/36110000000000000000 : ℝ)*(X 0 2+X 1 2)+(45810213263/144440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5223/1024 : ℝ)) (lo := (1987/20000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (36107833021039872047/36110000000000000000 : ℝ)) (alpha := (45810213263/144440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-559756961/5000000000 : ℝ)*X 0 0+(2711019289/5000000000 : ℝ)*X 0 1+(5422038587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612886899/5000000000 : ℝ)*X 1 0+(-21849993/156250000 : ℝ)*X 1 1+(84719353/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225773807/10000000000 : ℝ)*X 2 0+(5422038587/10000000000 : ℝ)*X 2 1+(-1398399547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((44993183/100000000 : ℝ)*X 0 0+(1973529707/5000000000 : ℝ)*X 0 1+(1973529713/5000000000 : ℝ)*X 0 2+(44993183/100000000 : ℝ)*X 1 0+(1973529707/5000000000 : ℝ)*X 1 1+(1973529713/5000000000 : ℝ)*X 1 2+(44993183/100000000 : ℝ)*X 2 0+(1973529707/5000000000 : ℝ)*X 2 1+(1973529713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-895904239/5000000000 : ℝ)*X 0 0+(32356289/62500000 : ℝ)*X 0 1+(2588503123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5392311359/10000000000 : ℝ)*X 1 0+(-752935103/5000000000 : ℝ)*X 1 1+(2588503119/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2696155679/5000000000 : ℝ)*X 2 0+(2588503121/5000000000 : ℝ)*X 2 1+(-1505870203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3718380401/10000000000 : ℝ)*X 0 0+(433668651/1000000000 : ℝ)*X 0 1+(542085813/1250000000 : ℝ)*X 0 2+(3718380401/10000000000 : ℝ)*X 1 0+(433668651/1000000000 : ℝ)*X 1 1+(542085813/1250000000 : ℝ)*X 1 2+(3718380401/10000000000 : ℝ)*X 2 0+(433668651/1000000000 : ℝ)*X 2 1+(542085813/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-823677189/5000000000 : ℝ)*X 0 0+(624577423/1250000000 : ℝ)*X 0 1+(1366288709/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196485291/10000000000 : ℝ)*X 1 0+(-137868501/1000000000 : ℝ)*X 1 1+(2732577489/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((519648539/1000000000 : ℝ)*X 2 0+(5465155003/10000000000 : ℝ)*X 2 1+(-1378684837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1157932357/2500000000 : ℝ)*X 0 0+(775664023/2000000000 : ℝ)*X 0 1+(1939160163/5000000000 : ℝ)*X 0 2+(1157932357/2500000000 : ℝ)*X 1 0+(775664023/2000000000 : ℝ)*X 1 1+(1939160163/5000000000 : ℝ)*X 1 2+(1157932357/2500000000 : ℝ)*X 2 0+(775664023/2000000000 : ℝ)*X 2 1+(1939160163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-15734837/125000000 : ℝ)*X 0 0+(1118741769/2000000000 : ℝ)*X 0 1+(5151793837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1352369097/2500000000 : ℝ)*X 1 0+(-758234867/5000000000 : ℝ)*X 1 1+(2575896939/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1352369123/2500000000 : ℝ)*X 2 0+(1030358759/2000000000 : ℝ)*X 2 1+(-189558713/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((181752141/500000000 : ℝ)*X 0 0+(4376669309/10000000000 : ℝ)*X 0 1+(4376669011/10000000000 : ℝ)*X 0 2+(181752141/500000000 : ℝ)*X 1 0+(4376669309/10000000000 : ℝ)*X 1 1+(4376669011/10000000000 : ℝ)*X 1 2+(181752141/500000000 : ℝ)*X 2 0+(4376669309/10000000000 : ℝ)*X 2 1+(4376669011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1701_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13333/20000 : ℝ) ≤ (-48143774718970119641038608286833/72220000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (752797/100000000000000 : ℝ)*(lower0) + (1582533/100000000000000 : ℝ)*(lower2) + (987377/100000000000000 : ℝ)*(lower3) + (88091/6250000000000 : ℝ)*(lower4) + (293327/100000000000000 : ℝ)*(lower5) + (53350512374329/4000000000000 : ℝ)*(major0) + (53350512374329/4000000000000 : ℝ)*(major1) + (53350512374329/4000000000000 : ℝ)*(major2) + (24839751/100000000000000 : ℝ)*(sp1) + (2467541/100000000000000 : ℝ)*(sp2) + (997519381732009/50000000000000 : ℝ)*(sp4) + (1995038738624267/100000000000000 : ℝ)*(sp5) + (498759690249119/25000000000000 : ℝ)*(sp6) + (694707742688487/100000000000000 : ℝ)*(sp7) + (694707742688487/100000000000000 : ℝ)*(f.failure) + (997519381732009/50000000000000 : ℝ)*(f.sum) + (58438130950451/7222000000000000000000000000 : ℝ)*base66 + (838289744034368537/144440000000000000000000000000000 : ℝ)*base68 + (181109870220208537/144440000000000000000000000000000 : ℝ)*base70 + (598339335395488537/144440000000000000000000000000000 : ℝ)*base72 + (86765206392977/7222000000000000000000000000 : ℝ)*base74 + (549806216812608537/144440000000000000000000000000000 : ℝ)*base76 + (476501284062848537/144440000000000000000000000000000 : ℝ)*base78 + (796046162843528537/144440000000000000000000000000000 : ℝ)*base80 + (19362509148929/7222000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12611081/2500000000000000000000 : ℝ)*base89 + (12611081/2500000000000000000000 : ℝ)*base91 + (12611081/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58191/100000 : ℝ) ≤ (1050680526140617023375586517138637/1805500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202031/100000000000000 : ℝ)*(upper0) + (46619/25000000000000 : ℝ)*(lower1) + (1207513/100000000000000 : ℝ)*(upper4) + (100221/5000000000000 : ℝ)*(upper5) + (1435968787341781/100000000000000 : ℝ)*(major0) + (1435968787341781/100000000000000 : ℝ)*(major1) + (1435968787341781/100000000000000 : ℝ)*(major2) + (210459673513001/10000000000000 : ℝ)*(sp0) + (1052298349622531/50000000000000 : ℝ)*(sp1) + (1052298370237227/50000000000000 : ℝ)*(sp2) + (37397148393931/5000000000000 : ℝ)*(sp3) + (41229391/100000000000000 : ℝ)*(sp5) + (905317/1000000000000 : ℝ)*(sp11) + (1336111/25000000000000 : ℝ)*(sp12) + (9349288230129/1250000000000 : ℝ)*(f.failure) + (1052298370237227/50000000000000 : ℝ)*(f.sum) + (14847097222323/7222000000000000000000000000 : ℝ)*base65 + (18367554703307845707/3611000000000000000000000000000000 : ℝ)*base67 + (11608533009049845707/3611000000000000000000000000000000 : ℝ)*base69 + (37361615817952845707/3611000000000000000000000000000000 : ℝ)*base71 + (30973294066383/7222000000000000000000000000 : ℝ)*base73 + (42365997309745845707/3611000000000000000000000000000000 : ℝ)*base75 + (24104231825289845707/3611000000000000000000000000000000 : ℝ)*base77 + (23654695907589845707/3611000000000000000000000000000000 : ℝ)*base79 + (55271737823399/7222000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (425573/31250000000000000000 : ℝ)*base90 + (425573/31250000000000000000 : ℝ)*base92 + (425573/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2537/3125 : ℝ) ≤ (1465822299246649505977722224289579/1805500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50025721/100000000000000 : ℝ)*(upper0) + (2225013/20000000000000 : ℝ)*(upper1) + (272967/12500000000000 : ℝ)*(upper3) + (45294249/100000000000000 : ℝ)*(upper4) + (1461238679683081/100000000000000 : ℝ)*(major0) + (1461238679683081/100000000000000 : ℝ)*(major1) + (1461238679683081/100000000000000 : ℝ)*(major2) + (9102926813/100000000000000 : ℝ)*(sp1) + (3470702679/20000000000000 : ℝ)*(sp2) + (858988063/100000000000000 : ℝ)*(sp3) + (266788747592553/12500000000000 : ℝ)*(sp8) + (2134300877813611/100000000000000 : ℝ)*(sp9) + (213429262722703/10000000000000 : ℝ)*(sp10) + (761104352200271/100000000000000 : ℝ)*(sp11) + (380552605594167/50000000000000 : ℝ)*(f.failure) + (266788747592553/12500000000000 : ℝ)*(f.sum) + (1785416732551/7222000000000000000000000000 : ℝ)*base65 + (25009327586083486807/3611000000000000000000000000000000 : ℝ)*base67 + (1428701301351513193/3611000000000000000000000000000000 : ℝ)*base70 + (16543105537683486807/3611000000000000000000000000000000 : ℝ)*base71 + (12211655177839/7222000000000000000000000000 : ℝ)*base74 + (5278324811641513193/3611000000000000000000000000000000 : ℝ)*base76 + (890883389893486807/3611000000000000000000000000000000 : ℝ)*base77 + (5141875909154486807/3611000000000000000000000000000000 : ℝ)*base79 + (6523911713939/1444400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7735079/1250000000000000000000 : ℝ)*base90 + (7735079/1250000000000000000000 : ℝ)*base92 + (7735079/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-45147/50000 : ℝ) ≤ (-1630207981869121705204987943536143/1805500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6769481/50000000000000 : ℝ)*(upper1) + (18731963/100000000000000 : ℝ)*(lower2) + (22472783/100000000000000 : ℝ)*(upper3) + (348991/1562500000000 : ℝ)*(upper5) + (1509516097318923/100000000000000 : ℝ)*(major0) + (1509516097318923/100000000000000 : ℝ)*(major1) + (1509516097318923/100000000000000 : ℝ)*(major2) + (136432941/100000000000000 : ℝ)*(sp4) + (349689213/12500000000000 : ℝ)*(sp6) + (1767551019/50000000000000 : ℝ)*(sp7) + (1131438999122253/50000000000000 : ℝ)*(sp12) + (282859766834681/12500000000000 : ℝ)*(sp13) + (70714854286367/3125000000000 : ℝ)*(sp14) + (157249519655947/20000000000000 : ℝ)*(sp15) + (393125566690887/50000000000000 : ℝ)*(f.failure) + (282859766834681/12500000000000 : ℝ)*(f.sum) + (14382316263389/7222000000000000000000000000 : ℝ)*base65 + (17649609603654095381/3611000000000000000000000000000000 : ℝ)*base67 + (10205611317914095381/3611000000000000000000000000000000 : ℝ)*base69 + (9347092519972904619/3611000000000000000000000000000000 : ℝ)*base72 + (14353375665563/7222000000000000000000000000 : ℝ)*base73 + (26223991660618095381/3611000000000000000000000000000000 : ℝ)*base75 + (3607257282388904619/3611000000000000000000000000000000 : ℝ)*base78 + (9187948111036095381/3611000000000000000000000000000000 : ℝ)*base79 + (29913811024871/7222000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5542281/1250000000000000000000 : ℝ)*base89 + (5542281/1250000000000000000000 : ℝ)*base91 + (5542281/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1701_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1987/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13333/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58191/100000 : ℝ) else (2537/3125 : ℝ) ≤ X j i ∧ X j i ≤ (45147/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1701_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1701_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13333/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58191/100000 : ℝ) else (2537/3125 : ℝ) ≤ X j i ∧ X j i ≤ (45147/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1701_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1701_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1701_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5223/1024 : ℝ) ≤ p) (hpb : p ≤ (5231/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47997263/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13333/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58191/100000 : ℝ) else (2537/3125 : ℝ) ≤ X j i ∧ X j i ≤ (45147/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1701_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
