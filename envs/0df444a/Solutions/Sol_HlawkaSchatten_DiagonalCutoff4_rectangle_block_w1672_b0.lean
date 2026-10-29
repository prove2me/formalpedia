-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1672_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:13.06777+00:00
-- url     : https://prove2.me/submissions/01316243-fc87-4880-82df-7ecbd805074f

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
theorem support_rectangle_w1672_s0_0 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1454822299/10000000000 : ℝ)*x 0 + (5758699373/10000000000 : ℝ)*x 1 + (2468049627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1454822299/10000000000 : ℝ)^5007 ≤ (8862873398137/100000000000000 : ℝ)^3983 := by
    have hnat : (1454822299 : ℕ)^5007*100000000000000^3983 ≤ 8862873398137^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454822299 10000000000 8862873398137 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5758699373/10000000000 : ℝ)^5007 ≤ (12492391441043/25000000000000 : ℝ)^3983 := by
    have hnat : (5758699373 : ℕ)^5007*25000000000000^3983 ≤ 12492391441043^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5758699373 10000000000 12492391441043 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2468049627/5000000000 : ℝ)^5007 ≤ (5145945103657/12500000000000 : ℝ)^3983 := by
    have hnat : (2468049627 : ℕ)^5007*12500000000000^3983 ≤ 5145945103657^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468049627 5000000000 5145945103657 12500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1454822299/10000000000 : ℝ), (5758699373/10000000000 : ℝ), (2468049627/5000000000 : ℝ)] ![(8862873398137/100000000000000 : ℝ), (12492391441043/25000000000000 : ℝ), (5145945103657/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1454822299/10000000000 : ℝ)|^5007 ≤ (8862873398137/100000000000000 : ℝ)^3983
        have hw : |(-1454822299/10000000000 : ℝ)|=(1454822299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5758699373/10000000000 : ℝ)|^5007 ≤ (12492391441043/25000000000000 : ℝ)^3983
        have hw : |(5758699373/10000000000 : ℝ)|=(5758699373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2468049627/5000000000 : ℝ)|^5007 ≤ (5145945103657/12500000000000 : ℝ)^3983
        have hw : |(2468049627/5000000000 : ℝ)|=(2468049627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s0_1 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2714457151/5000000000 : ℝ)*x 0 + (-952196081/5000000000 : ℝ)*x 1 + (4936100333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2714457151/5000000000 : ℝ)^5007 ≤ (46399109590921/100000000000000 : ℝ)^3983 := by
    have hnat : (2714457151 : ℕ)^5007*100000000000000^3983 ≤ 46399109590921^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714457151 5000000000 46399109590921 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (952196081/5000000000 : ℝ)^5007 ≤ (6216659126533/50000000000000 : ℝ)^3983 := by
    have hnat : (952196081 : ℕ)^5007*50000000000000^3983 ≤ 6216659126533^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952196081 5000000000 6216659126533 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4936100333/10000000000 : ℝ)^5007 ≤ (41167572141793/100000000000000 : ℝ)^3983 := by
    have hnat : (4936100333 : ℕ)^5007*100000000000000^3983 ≤ 41167572141793^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936100333 10000000000 41167572141793 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2714457151/5000000000 : ℝ), (-952196081/5000000000 : ℝ), (4936100333/10000000000 : ℝ)] ![(46399109590921/100000000000000 : ℝ), (6216659126533/50000000000000 : ℝ), (41167572141793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2714457151/5000000000 : ℝ)|^5007 ≤ (46399109590921/100000000000000 : ℝ)^3983
        have hw : |(2714457151/5000000000 : ℝ)|=(2714457151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-952196081/5000000000 : ℝ)|^5007 ≤ (6216659126533/50000000000000 : ℝ)^3983
        have hw : |(-952196081/5000000000 : ℝ)|=(952196081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4936100333/10000000000 : ℝ)|^5007 ≤ (41167572141793/100000000000000 : ℝ)^3983
        have hw : |(4936100333/10000000000 : ℝ)|=(4936100333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s0_2 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5428916811/10000000000 : ℝ)*x 0 + (4936098849/10000000000 : ℝ)*x 1 + (-952195387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5428916811/10000000000 : ℝ)^5007 ≤ (46399136547491/100000000000000 : ℝ)^3983 := by
    have hnat : (5428916811 : ℕ)^5007*100000000000000^3983 ≤ 46399136547491^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428916811 10000000000 46399136547491 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4936098849/10000000000 : ℝ)^5007 ≤ (10291889145781/25000000000000 : ℝ)^3983 := by
    have hnat : (4936098849 : ℕ)^5007*25000000000000^3983 ≤ 10291889145781^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936098849 10000000000 10291889145781 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952195387/5000000000 : ℝ)^5007 ≤ (3108326715349/25000000000000 : ℝ)^3983 := by
    have hnat : (952195387 : ℕ)^5007*25000000000000^3983 ≤ 3108326715349^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952195387 5000000000 3108326715349 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5428916811/10000000000 : ℝ), (4936098849/10000000000 : ℝ), (-952195387/5000000000 : ℝ)] ![(46399136547491/100000000000000 : ℝ), (10291889145781/25000000000000 : ℝ), (3108326715349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5428916811/10000000000 : ℝ)|^5007 ≤ (46399136547491/100000000000000 : ℝ)^3983
        have hw : |(5428916811/10000000000 : ℝ)|=(5428916811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4936098849/10000000000 : ℝ)|^5007 ≤ (10291889145781/25000000000000 : ℝ)^3983
        have hw : |(4936098849/10000000000 : ℝ)|=(4936098849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952195387/5000000000 : ℝ)|^5007 ≤ (3108326715349/25000000000000 : ℝ)^3983
        have hw : |(-952195387/5000000000 : ℝ)|=(952195387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s0_3 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4080436483/10000000000 : ℝ)*x 0 + (1544257607/5000000000 : ℝ)*x 1 + (1055177027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4080436483/10000000000 : ℝ)^5007 ≤ (3240575603827/10000000000000 : ℝ)^3983 := by
    have hnat : (4080436483 : ℕ)^5007*10000000000000^3983 ≤ 3240575603827^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4080436483 10000000000 3240575603827 10000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1544257607/5000000000 : ℝ)^5007 ≤ (4566654481897/20000000000000 : ℝ)^3983 := by
    have hnat : (1544257607 : ℕ)^5007*20000000000000^3983 ≤ 4566654481897^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544257607 5000000000 4566654481897 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055177027/2000000000 : ℝ)^5007 ≤ (44760971532987/100000000000000 : ℝ)^3983 := by
    have hnat : (1055177027 : ℕ)^5007*100000000000000^3983 ≤ 44760971532987^3983*2000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055177027 2000000000 44760971532987 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4080436483/10000000000 : ℝ), (1544257607/5000000000 : ℝ), (1055177027/2000000000 : ℝ)] ![(3240575603827/10000000000000 : ℝ), (4566654481897/20000000000000 : ℝ), (44760971532987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4080436483/10000000000 : ℝ)|^5007 ≤ (3240575603827/10000000000000 : ℝ)^3983
        have hw : |(4080436483/10000000000 : ℝ)|=(4080436483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1544257607/5000000000 : ℝ)|^5007 ≤ (4566654481897/20000000000000 : ℝ)^3983
        have hw : |(1544257607/5000000000 : ℝ)|=(1544257607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055177027/2000000000 : ℝ)|^5007 ≤ (44760971532987/100000000000000 : ℝ)^3983
        have hw : |(1055177027/2000000000 : ℝ)|=(1055177027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s0_4 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-291376599/2000000000 : ℝ)*x 0 + (619532057/1250000000 : ℝ)*x 1 + (1434464609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291376599/2000000000 : ℝ)^5007 ≤ (8878657680861/100000000000000 : ℝ)^3983 := by
    have hnat : (291376599 : ℕ)^5007*100000000000000^3983 ≤ 8878657680861^3983*2000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291376599 2000000000 8878657680861 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (619532057/1250000000 : ℝ)^5007 ≤ (1655160214707/4000000000000 : ℝ)^3983 := by
    have hnat : (619532057 : ℕ)^5007*4000000000000^3983 ≤ 1655160214707^3983*1250000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619532057 1250000000 1655160214707 4000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1434464609/2500000000 : ℝ)^5007 ≤ (24871168468791/50000000000000 : ℝ)^3983 := by
    have hnat : (1434464609 : ℕ)^5007*50000000000000^3983 ≤ 24871168468791^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434464609 2500000000 24871168468791 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291376599/2000000000 : ℝ), (619532057/1250000000 : ℝ), (1434464609/2500000000 : ℝ)] ![(8878657680861/100000000000000 : ℝ), (1655160214707/4000000000000 : ℝ), (24871168468791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291376599/2000000000 : ℝ)|^5007 ≤ (8878657680861/100000000000000 : ℝ)^3983
        have hw : |(-291376599/2000000000 : ℝ)|=(291376599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(619532057/1250000000 : ℝ)|^5007 ≤ (1655160214707/4000000000000 : ℝ)^3983
        have hw : |(619532057/1250000000 : ℝ)|=(619532057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1434464609/2500000000 : ℝ)|^5007 ≤ (24871168468791/50000000000000 : ℝ)^3983
        have hw : |(1434464609/2500000000 : ℝ)|=(1434464609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s0_5 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204635661/10000000000 : ℝ)*x 0 + (-551317411/5000000000 : ℝ)*x 1 + (1434463807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204635661/10000000000 : ℝ)^5007 ≤ (44002400952477/100000000000000 : ℝ)^3983 := by
    have hnat : (5204635661 : ℕ)^5007*100000000000000^3983 ≤ 44002400952477^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204635661 10000000000 44002400952477 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551317411/5000000000 : ℝ)^5007 ≤ (6255297059333/100000000000000 : ℝ)^3983 := by
    have hnat : (551317411 : ℕ)^5007*100000000000000^3983 ≤ 6255297059333^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551317411 5000000000 6255297059333 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1434463807/2500000000 : ℝ)^5007 ≤ (9948460395411/20000000000000 : ℝ)^3983 := by
    have hnat : (1434463807 : ℕ)^5007*20000000000000^3983 ≤ 9948460395411^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434463807 2500000000 9948460395411 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204635661/10000000000 : ℝ), (-551317411/5000000000 : ℝ), (1434463807/2500000000 : ℝ)] ![(44002400952477/100000000000000 : ℝ), (6255297059333/100000000000000 : ℝ), (9948460395411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204635661/10000000000 : ℝ)|^5007 ≤ (44002400952477/100000000000000 : ℝ)^3983
        have hw : |(5204635661/10000000000 : ℝ)|=(5204635661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551317411/5000000000 : ℝ)|^5007 ≤ (6255297059333/100000000000000 : ℝ)^3983
        have hw : |(-551317411/5000000000 : ℝ)|=(551317411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1434463807/2500000000 : ℝ)|^5007 ≤ (9948460395411/20000000000000 : ℝ)^3983
        have hw : |(1434463807/2500000000 : ℝ)|=(1434463807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s0_6 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301158933/2500000000 : ℝ)*x 0 + (2868927171/5000000000 : ℝ)*x 1 + (-110263607/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301158933/2500000000 : ℝ)^5007 ≤ (44002401707069/100000000000000 : ℝ)^3983 := by
    have hnat : (1301158933 : ℕ)^5007*100000000000000^3983 ≤ 44002401707069^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301158933 2500000000 44002401707069 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2868927171/5000000000 : ℝ)^5007 ≤ (49742292321499/100000000000000 : ℝ)^3983 := by
    have hnat : (2868927171 : ℕ)^5007*100000000000000^3983 ≤ 49742292321499^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868927171 5000000000 49742292321499 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110263607/1000000000 : ℝ)^5007 ≤ (12510611919/200000000000 : ℝ)^3983 := by
    have hnat : (110263607 : ℕ)^5007*200000000000^3983 ≤ 12510611919^3983*1000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110263607 1000000000 12510611919 200000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301158933/2500000000 : ℝ), (2868927171/5000000000 : ℝ), (-110263607/1000000000 : ℝ)] ![(44002401707069/100000000000000 : ℝ), (49742292321499/100000000000000 : ℝ), (12510611919/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301158933/2500000000 : ℝ)|^5007 ≤ (44002401707069/100000000000000 : ℝ)^3983
        have hw : |(1301158933/2500000000 : ℝ)|=(1301158933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2868927171/5000000000 : ℝ)|^5007 ≤ (49742292321499/100000000000000 : ℝ)^3983
        have hw : |(2868927171/5000000000 : ℝ)|=(2868927171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110263607/1000000000 : ℝ)|^5007 ≤ (12510611919/200000000000 : ℝ)^3983
        have hw : |(-110263607/1000000000 : ℝ)|=(110263607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s0_7 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2042955989/5000000000 : ℝ)*x 0 + (208891333/400000000 : ℝ)*x 1 + (785984301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042955989/5000000000 : ℝ)^5007 ≤ (32460430068709/100000000000000 : ℝ)^3983 := by
    have hnat : (2042955989 : ℕ)^5007*100000000000000^3983 ≤ 32460430068709^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042955989 5000000000 32460430068709 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208891333/400000000 : ℝ)^5007 ≤ (44190042777501/100000000000000 : ℝ)^3983 := by
    have hnat : (208891333 : ℕ)^5007*100000000000000^3983 ≤ 44190042777501^3983*400000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208891333 400000000 44190042777501 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (785984301/2500000000 : ℝ)^5007 ≤ (11674763568761/50000000000000 : ℝ)^3983 := by
    have hnat : (785984301 : ℕ)^5007*50000000000000^3983 ≤ 11674763568761^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785984301 2500000000 11674763568761 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2042955989/5000000000 : ℝ), (208891333/400000000 : ℝ), (785984301/2500000000 : ℝ)] ![(32460430068709/100000000000000 : ℝ), (44190042777501/100000000000000 : ℝ), (11674763568761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2042955989/5000000000 : ℝ)|^5007 ≤ (32460430068709/100000000000000 : ℝ)^3983
        have hw : |(2042955989/5000000000 : ℝ)|=(2042955989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208891333/400000000 : ℝ)|^5007 ≤ (44190042777501/100000000000000 : ℝ)^3983
        have hw : |(208891333/400000000 : ℝ)|=(208891333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(785984301/2500000000 : ℝ)|^5007 ≤ (11674763568761/50000000000000 : ℝ)^3983
        have hw : |(785984301/2500000000 : ℝ)|=(785984301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1672_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5257/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22899/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
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
  have hpowlo : (0 : ℝ) ^ (5003/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5003 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5003*1^1024 ≤ 0^1024*1^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5003/1024 : ℝ) ≤ (1137018972693878241/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5003 ≤ (1137018972693878241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5003*100000000000000000000^1024 ≤ 1137018972693878241^1024*5^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1137018972693878241 100000000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1137018972693878241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5003 := by
      have hnat : (1 : ℕ)^1024*1^5003 ≤ 1^5003*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101137018972693878241/100000000000000000000 : ℝ) ≤ (2505791917687307/2500000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (101137018972693878241/100000000000000000000 : ℝ)^1024 ≤ (2505791917687307/2500000000000000 : ℝ)^5003 := by
      have hnat : (101137018972693878241 : ℕ)^1024*2500000000000000^5003 ≤ 2505791917687307^5003*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101137018972693878241 100000000000000000000 2505791917687307 2500000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505791917687307/2500000000000000 : ℝ)) (X := (101137018972693878241/100000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51137018972693878241/50000000000000000000 : ℝ) ≤ (1255791917687307/1250000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (51137018972693878241/50000000000000000000 : ℝ)^1024 ≤ (1255791917687307/1250000000000000 : ℝ)^5003 := by
      have hnat : (51137018972693878241 : ℕ)^1024*1250000000000000^5003 ≤ 1255791917687307^5003*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51137018972693878241 50000000000000000000 1255791917687307 1250000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255791917687307/1250000000000000 : ℝ)) (X := (51137018972693878241/50000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5791917687307/1000000000000000 : ℝ)*(0 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5791917687307/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1137018972693878241/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5791917687307/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5003/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5791917687307/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2505791917687307/2500000000000000 : ℝ) by norm_num, show 1+(1137018972693878241/100000000000000000000 : ℝ)+(0 : ℝ)=(101137018972693878241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1137018972693878241/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5791917687307/1000000000000000 : ℝ)*(2/5 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5791917687307/1000000000000000 : ℝ)*(2/5 : ℝ)=(1255791917687307/1250000000000000 : ℝ) by norm_num, show 1+2*(1137018972693878241/100000000000000000000 : ℝ)=(51137018972693878241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5791917687307/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5791917687307/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5791917687307/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5791917687307/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5791917687307/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5791917687307/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1454822299/10000000000 : ℝ)*X 0 0+(5758699373/10000000000 : ℝ)*X 0 1+(2468049627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2714457151/5000000000 : ℝ)*X 1 0+(-952196081/5000000000 : ℝ)*X 1 1+(4936100333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5428916811/10000000000 : ℝ)*X 2 0+(4936098849/10000000000 : ℝ)*X 2 1+(-952195387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4080436483/10000000000 : ℝ)*X 0 0+(1544257607/5000000000 : ℝ)*X 0 1+(1055177027/2000000000 : ℝ)*X 0 2+(4080436483/10000000000 : ℝ)*X 1 0+(1544257607/5000000000 : ℝ)*X 1 1+(1055177027/2000000000 : ℝ)*X 1 2+(4080436483/10000000000 : ℝ)*X 2 0+(1544257607/5000000000 : ℝ)*X 2 1+(1055177027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-291376599/2000000000 : ℝ)*X 0 0+(619532057/1250000000 : ℝ)*X 0 1+(1434464609/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5204635661/10000000000 : ℝ)*X 1 0+(-551317411/5000000000 : ℝ)*X 1 1+(1434463807/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1301158933/2500000000 : ℝ)*X 2 0+(2868927171/5000000000 : ℝ)*X 2 1+(-110263607/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2042955989/5000000000 : ℝ)*X 0 0+(208891333/400000000 : ℝ)*X 0 1+(785984301/2500000000 : ℝ)*X 0 2+(2042955989/5000000000 : ℝ)*X 1 0+(208891333/400000000 : ℝ)*X 1 1+(785984301/2500000000 : ℝ)*X 1 2+(2042955989/5000000000 : ℝ)*X 2 0+(208891333/400000000 : ℝ)*X 2 1+(785984301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16869352658871136452567/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21726349/100000000000000 : ℝ)*(base1) + (37624639/20000000000000 : ℝ)*(base19) + (511302069/100000000000000 : ℝ)*(base23) + (10240893/6250000000000 : ℝ)*(base24) + (40603179/100000000000000 : ℝ)*(base51) + (836416778356727/100000000000000 : ℝ)*(major0) + (836416778356727/100000000000000 : ℝ)*(major1) + (836416778356727/100000000000000 : ℝ)*(major2) + (1215658864454783/100000000000000 : ℝ)*(sp0) + (607830672527227/50000000000000 : ℝ)*(sp1) + (303915214505323/25000000000000 : ℝ)*(sp2) + (228585370454213/50000000000000 : ℝ)*(sp3) + (42038269/1562500000000 : ℝ)*(sp4) + (602334923/50000000000000 : ℝ)*(sp7) + (228585983652311/50000000000000 : ℝ)*(f.failure) + (24313230663553/2000000000000 : ℝ)*(f.sum) + (175753969485811/50000000000000000000000000000 : ℝ)*base66 + (530842380935811/100000000000000000000000000000 : ℝ)*base68 + (398563929235811/100000000000000000000000000000 : ℝ)*base70 + (95014539435811/100000000000000000000000000000 : ℝ)*base72 + (89998392335811/50000000000000000000000000000 : ℝ)*base74 + (13995441635811/100000000000000000000000000000 : ℝ)*base76 + (499548409835811/100000000000000000000000000000 : ℝ)*base78 + (2197283764189/100000000000000000000000000000 : ℝ)*base79 + (140424218335811/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1397393/125000000000000000000 : ℝ)*base89 + (1397393/125000000000000000000 : ℝ)*base91 + (1397393/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2921720398894413835689/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (101540363/10000000000000 : ℝ)*(base19) + (611539331/50000000000000 : ℝ)*(base23) + (131308719/100000000000000 : ℝ)*(upper2) + (9620299/100000000000000 : ℝ)*(upper3) + (9418467/25000000000000 : ℝ)*(upper5) + (110036068992739/12500000000000 : ℝ)*(major0) + (110036068992739/12500000000000 : ℝ)*(major1) + (110036068992739/12500000000000 : ℝ)*(major2) + (1281755217/100000000000000 : ℝ)*(sp0) + (360102759/25000000000000 : ℝ)*(sp1) + (63971206193711/5000000000000 : ℝ)*(sp4) + (319855737453693/25000000000000 : ℝ)*(sp5) + (159928022818847/12500000000000 : ℝ)*(sp6) + (481151573594307/100000000000000 : ℝ)*(sp7) + (481151573594307/100000000000000 : ℝ)*(f.failure) + (639712702814719/50000000000000 : ℝ)*(f.sum) + (20262877570123/6250000000000000000000000000 : ℝ)*base65 + (42794680013873/12500000000000000000000000000 : ℝ)*base67 + (72685284638873/12500000000000000000000000000 : ℝ)*base69 + (62377725338873/12500000000000000000000000000 : ℝ)*base71 + (13432771779877/6250000000000000000000000000 : ℝ)*base74 + (36009347563873/12500000000000000000000000000 : ℝ)*base75 + (63888889488873/12500000000000000000000000000 : ℝ)*base77 + (47510603376373/12500000000000000000000000000 : ℝ)*base79 + (6361940211127/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2202059/250000000000000000000 : ℝ)*base90 + (2202059/250000000000000000000 : ℝ)*base92 + (2202059/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1672_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22899/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1672_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1672_s1_0 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1551924191/10000000000 : ℝ)*x 0 + (1096141317/2000000000 : ℝ)*x 1 + (2575398787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1551924191/10000000000 : ℝ)^5007 ≤ (1201598214471/12500000000000 : ℝ)^3983 := by
    have hnat : (1551924191 : ℕ)^5007*12500000000000^3983 ≤ 1201598214471^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551924191 10000000000 1201598214471 12500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096141317/2000000000 : ℝ)^5007 ≤ (46956244044387/100000000000000 : ℝ)^3983 := by
    have hnat : (1096141317 : ℕ)^5007*100000000000000^3983 ≤ 46956244044387^3983*2000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096141317 2000000000 46956244044387 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575398787/5000000000 : ℝ)^5007 ≤ (21715485115611/50000000000000 : ℝ)^3983 := by
    have hnat : (2575398787 : ℕ)^5007*50000000000000^3983 ≤ 21715485115611^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575398787 5000000000 21715485115611 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1551924191/10000000000 : ℝ), (1096141317/2000000000 : ℝ), (2575398787/5000000000 : ℝ)] ![(1201598214471/12500000000000 : ℝ), (46956244044387/100000000000000 : ℝ), (21715485115611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1551924191/10000000000 : ℝ)|^5007 ≤ (1201598214471/12500000000000 : ℝ)^3983
        have hw : |(-1551924191/10000000000 : ℝ)|=(1551924191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096141317/2000000000 : ℝ)|^5007 ≤ (46956244044387/100000000000000 : ℝ)^3983
        have hw : |(1096141317/2000000000 : ℝ)|=(1096141317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575398787/5000000000 : ℝ)|^5007 ≤ (21715485115611/50000000000000 : ℝ)^3983
        have hw : |(2575398787/5000000000 : ℝ)|=(2575398787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s1_1 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677479097/5000000000 : ℝ)*x 0 + (-430745027/2500000000 : ℝ)*x 1 + (5150797631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677479097/5000000000 : ℝ)^5007 ≤ (11401481267191/25000000000000 : ℝ)^3983 := by
    have hnat : (2677479097 : ℕ)^5007*25000000000000^3983 ≤ 11401481267191^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677479097 5000000000 11401481267191 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430745027/2500000000 : ℝ)^5007 ≤ (10963104084913/100000000000000 : ℝ)^3983 := by
    have hnat : (430745027 : ℕ)^5007*100000000000000^3983 ≤ 10963104084913^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430745027 2500000000 10963104084913 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150797631/10000000000 : ℝ)^5007 ≤ (43430970835403/100000000000000 : ℝ)^3983 := by
    have hnat : (5150797631 : ℕ)^5007*100000000000000^3983 ≤ 43430970835403^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150797631 10000000000 43430970835403 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677479097/5000000000 : ℝ), (-430745027/2500000000 : ℝ), (5150797631/10000000000 : ℝ)] ![(11401481267191/25000000000000 : ℝ), (10963104084913/100000000000000 : ℝ), (43430970835403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677479097/5000000000 : ℝ)|^5007 ≤ (11401481267191/25000000000000 : ℝ)^3983
        have hw : |(2677479097/5000000000 : ℝ)|=(2677479097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430745027/2500000000 : ℝ)|^5007 ≤ (10963104084913/100000000000000 : ℝ)^3983
        have hw : |(-430745027/2500000000 : ℝ)|=(430745027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150797631/10000000000 : ℝ)|^5007 ≤ (43430970835403/100000000000000 : ℝ)^3983
        have hw : |(5150797631/10000000000 : ℝ)|=(5150797631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s1_2 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354958119/10000000000 : ℝ)*x 0 + (2575398893/5000000000 : ℝ)*x 1 + (-1722980003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354958119/10000000000 : ℝ)^5007 ≤ (11401481066451/25000000000000 : ℝ)^3983 := by
    have hnat : (5354958119 : ℕ)^5007*25000000000000^3983 ≤ 11401481066451^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354958119 10000000000 11401481066451 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575398893/5000000000 : ℝ)^5007 ≤ (2714435779897/6250000000000 : ℝ)^3983 := by
    have hnat : (2575398893 : ℕ)^5007*6250000000000^3983 ≤ 2714435779897^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575398893 5000000000 2714435779897 6250000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722980003/10000000000 : ℝ)^5007 ≤ (10963103245047/100000000000000 : ℝ)^3983 := by
    have hnat : (1722980003 : ℕ)^5007*100000000000000^3983 ≤ 10963103245047^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722980003 10000000000 10963103245047 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354958119/10000000000 : ℝ), (2575398893/5000000000 : ℝ), (-1722980003/10000000000 : ℝ)] ![(11401481066451/25000000000000 : ℝ), (2714435779897/6250000000000 : ℝ), (10963103245047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354958119/10000000000 : ℝ)|^5007 ≤ (11401481066451/25000000000000 : ℝ)^3983
        have hw : |(5354958119/10000000000 : ℝ)|=(5354958119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575398893/5000000000 : ℝ)|^5007 ≤ (2714435779897/6250000000000 : ℝ)^3983
        have hw : |(2575398893/5000000000 : ℝ)|=(2575398893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722980003/10000000000 : ℝ)|^5007 ≤ (10963103245047/100000000000000 : ℝ)^3983
        have hw : |(-1722980003/10000000000 : ℝ)|=(1722980003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s1_3 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (831661259/2000000000 : ℝ)*x 0 + (933975117/2500000000 : ℝ)*x 1 + (230657911/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831661259/2000000000 : ℝ)^5007 ≤ (33185067468889/100000000000000 : ℝ)^3983 := by
    have hnat : (831661259 : ℕ)^5007*100000000000000^3983 ≤ 33185067468889^3983*2000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831661259 2000000000 33185067468889 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933975117/2500000000 : ℝ)^5007 ≤ (29004225548149/100000000000000 : ℝ)^3983 := by
    have hnat : (933975117 : ℕ)^5007*100000000000000^3983 ≤ 29004225548149^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933975117 2500000000 29004225548149 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230657911/500000000 : ℝ)^5007 ≤ (7562141392541/20000000000000 : ℝ)^3983 := by
    have hnat : (230657911 : ℕ)^5007*20000000000000^3983 ≤ 7562141392541^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230657911 500000000 7562141392541 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(831661259/2000000000 : ℝ), (933975117/2500000000 : ℝ), (230657911/500000000 : ℝ)] ![(33185067468889/100000000000000 : ℝ), (29004225548149/100000000000000 : ℝ), (7562141392541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(831661259/2000000000 : ℝ)|^5007 ≤ (33185067468889/100000000000000 : ℝ)^3983
        have hw : |(831661259/2000000000 : ℝ)|=(831661259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933975117/2500000000 : ℝ)|^5007 ≤ (29004225548149/100000000000000 : ℝ)^3983
        have hw : |(933975117/2500000000 : ℝ)|=(933975117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230657911/500000000 : ℝ)|^5007 ≤ (7562141392541/20000000000000 : ℝ)^3983
        have hw : |(230657911/500000000 : ℝ)|=(230657911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s1_4 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-776027891/5000000000 : ℝ)*x 0 + (2577018651/5000000000 : ℝ)*x 1 + (5477422507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (776027891/5000000000 : ℝ)^5007 ≤ (4806905184559/50000000000000 : ℝ)^3983 := by
    have hnat : (776027891 : ℕ)^5007*50000000000000^3983 ≤ 4806905184559^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776027891 5000000000 4806905184559 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577018651/5000000000 : ℝ)^5007 ≤ (43465313054121/100000000000000 : ℝ)^3983 := by
    have hnat : (2577018651 : ℕ)^5007*100000000000000^3983 ≤ 43465313054121^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577018651 5000000000 43465313054121 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477422507/10000000000 : ℝ)^5007 ≤ (11730219141657/25000000000000 : ℝ)^3983 := by
    have hnat : (5477422507 : ℕ)^5007*25000000000000^3983 ≤ 11730219141657^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477422507 10000000000 11730219141657 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-776027891/5000000000 : ℝ), (2577018651/5000000000 : ℝ), (5477422507/10000000000 : ℝ)] ![(4806905184559/50000000000000 : ℝ), (43465313054121/100000000000000 : ℝ), (11730219141657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-776027891/5000000000 : ℝ)|^5007 ≤ (4806905184559/50000000000000 : ℝ)^3983
        have hw : |(-776027891/5000000000 : ℝ)|=(776027891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577018651/5000000000 : ℝ)|^5007 ≤ (43465313054121/100000000000000 : ℝ)^3983
        have hw : |(2577018651/5000000000 : ℝ)|=(2577018651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477422507/10000000000 : ℝ)|^5007 ≤ (11730219141657/25000000000000 : ℝ)^3983
        have hw : |(5477422507/10000000000 : ℝ)|=(5477422507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s1_5 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316643131/2500000000 : ℝ)*x 0 + (-349088753/2500000000 : ℝ)*x 1 + (1369355633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316643131/2500000000 : ℝ)^5007 ≤ (44661672658973/100000000000000 : ℝ)^3983 := by
    have hnat : (1316643131 : ℕ)^5007*100000000000000^3983 ≤ 44661672658973^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316643131 2500000000 44661672658973 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349088753/2500000000 : ℝ)^5007 ≤ (526090655359/6250000000000 : ℝ)^3983 := by
    have hnat : (349088753 : ℕ)^5007*6250000000000^3983 ≤ 526090655359^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349088753 2500000000 526090655359 6250000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369355633/2500000000 : ℝ)^5007 ≤ (46920876835841/100000000000000 : ℝ)^3983 := by
    have hnat : (1369355633 : ℕ)^5007*100000000000000^3983 ≤ 46920876835841^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369355633 2500000000 46920876835841 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316643131/2500000000 : ℝ), (-349088753/2500000000 : ℝ), (1369355633/2500000000 : ℝ)] ![(44661672658973/100000000000000 : ℝ), (526090655359/6250000000000 : ℝ), (46920876835841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316643131/2500000000 : ℝ)|^5007 ≤ (44661672658973/100000000000000 : ℝ)^3983
        have hw : |(1316643131/2500000000 : ℝ)|=(1316643131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349088753/2500000000 : ℝ)|^5007 ≤ (526090655359/6250000000000 : ℝ)^3983
        have hw : |(-349088753/2500000000 : ℝ)|=(349088753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369355633/2500000000 : ℝ)|^5007 ≤ (46920876835841/100000000000000 : ℝ)^3983
        have hw : |(1369355633/2500000000 : ℝ)|=(1369355633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s1_6 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633286229/5000000000 : ℝ)*x 0 + (2738711251/5000000000 : ℝ)*x 1 + (-1396355147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633286229/5000000000 : ℝ)^5007 ≤ (8932334391077/20000000000000 : ℝ)^3983 := by
    have hnat : (2633286229 : ℕ)^5007*20000000000000^3983 ≤ 8932334391077^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633286229 5000000000 8932334391077 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738711251/5000000000 : ℝ)^5007 ≤ (9384175302557/20000000000000 : ℝ)^3983 := by
    have hnat : (2738711251 : ℕ)^5007*20000000000000^3983 ≤ 9384175302557^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738711251 5000000000 9384175302557 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396355147/10000000000 : ℝ)^5007 ≤ (263045359649/3125000000000 : ℝ)^3983 := by
    have hnat : (1396355147 : ℕ)^5007*3125000000000^3983 ≤ 263045359649^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396355147 10000000000 263045359649 3125000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633286229/5000000000 : ℝ), (2738711251/5000000000 : ℝ), (-1396355147/10000000000 : ℝ)] ![(8932334391077/20000000000000 : ℝ), (9384175302557/20000000000000 : ℝ), (263045359649/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633286229/5000000000 : ℝ)|^5007 ≤ (8932334391077/20000000000000 : ℝ)^3983
        have hw : |(2633286229/5000000000 : ℝ)|=(2633286229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738711251/5000000000 : ℝ)|^5007 ≤ (9384175302557/20000000000000 : ℝ)^3983
        have hw : |(2738711251/5000000000 : ℝ)|=(2738711251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1396355147/10000000000 : ℝ)|^5007 ≤ (263045359649/3125000000000 : ℝ)^3983
        have hw : |(-1396355147/10000000000 : ℝ)|=(1396355147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s1_7 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2079327407/5000000000 : ℝ)*x 0 + (4604542897/10000000000 : ℝ)*x 1 + (936158203/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079327407/5000000000 : ℝ)^5007 ≤ (6637712779479/20000000000000 : ℝ)^3983 := by
    have hnat : (2079327407 : ℕ)^5007*20000000000000^3983 ≤ 6637712779479^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079327407 5000000000 6637712779479 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4604542897/10000000000 : ℝ)^5007 ≤ (9430490128859/25000000000000 : ℝ)^3983 := by
    have hnat : (4604542897 : ℕ)^5007*25000000000000^3983 ≤ 9430490128859^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604542897 10000000000 9430490128859 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936158203/2500000000 : ℝ)^5007 ≤ (14544737784413/50000000000000 : ℝ)^3983 := by
    have hnat : (936158203 : ℕ)^5007*50000000000000^3983 ≤ 14544737784413^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936158203 2500000000 14544737784413 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079327407/5000000000 : ℝ), (4604542897/10000000000 : ℝ), (936158203/2500000000 : ℝ)] ![(6637712779479/20000000000000 : ℝ), (9430490128859/25000000000000 : ℝ), (14544737784413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079327407/5000000000 : ℝ)|^5007 ≤ (6637712779479/20000000000000 : ℝ)^3983
        have hw : |(2079327407/5000000000 : ℝ)|=(2079327407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4604542897/10000000000 : ℝ)|^5007 ≤ (9430490128859/25000000000000 : ℝ)^3983
        have hw : |(4604542897/10000000000 : ℝ)|=(4604542897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(936158203/2500000000 : ℝ)|^5007 ≤ (14544737784413/50000000000000 : ℝ)^3983
        have hw : |(936158203/2500000000 : ℝ)|=(936158203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1672_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5017/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8527/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5257/100000 : ℝ) ^ (5003/1024 : ℝ) ≤ (1756732302613/3125000000000000000 : ℝ) := by
    have hpowers : (5257/100000 : ℝ)^5003 ≤ (1756732302613/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5257 : ℕ)^5003*3125000000000000000^1024 ≤ 1756732302613^1024*100000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5257 100000 1756732302613 3125000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5257/100000 : ℝ)) (X := (1756732302613/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22899/100000 : ℝ) ^ (5003/1024 : ℝ) ≤ (9314049954353843/12500000000000000000 : ℝ) := by
    have hpowers : (22899/100000 : ℝ)^5003 ≤ (9314049954353843/12500000000000000000 : ℝ)^1024 := by
      have hnat : (22899 : ℕ)^5003*12500000000000000000^1024 ≤ 9314049954353843^1024*100000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22899 100000 9314049954353843 12500000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22899/100000 : ℝ)) (X := (9314049954353843/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562501756732302613/1562500000000000000 : ℝ) ≤ (10000002301202413/10000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (1562501756732302613/1562500000000000000 : ℝ)^1024 ≤ (10000002301202413/10000000000000000 : ℝ)^5003 := by
      have hnat : (1562501756732302613 : ℕ)^1024*10000000000000000^5003 ≤ 10000002301202413^5003*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562501756732302613 1562500000000000000 10000002301202413 10000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002301202413/10000000000000000 : ℝ)) (X := (1562501756732302613/1562500000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501864215376712859/2500000000000000000 : ℝ) ≤ (2500381449277273/2500000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (2501864215376712859/2500000000000000000 : ℝ)^1024 ≤ (2500381449277273/2500000000000000 : ℝ)^5003 := by
      have hnat : (2501864215376712859 : ℕ)^1024*2500000000000000^5003 ≤ 2500381449277273^5003*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501864215376712859 2500000000000000000 2500381449277273 2500000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500381449277273/2500000000000000 : ℝ)) (X := (2501864215376712859/2500000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6259314049954353843/6250000000000000000 : ℝ) ≤ (10003049293015771/10000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (6259314049954353843/6250000000000000000 : ℝ)^1024 ≤ (10003049293015771/10000000000000000 : ℝ)^5003 := by
      have hnat : (6259314049954353843 : ℕ)^1024*10000000000000000^5003 ≤ 10003049293015771^5003*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259314049954353843 6250000000000000000 10003049293015771 10000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003049293015771/10000000000000000 : ℝ)) (X := (6259314049954353843/6250000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1756732302613/3125000000000000000 : ℝ) ≤ ((8820201128092507357/8821000000000000000 : ℝ)+2*(1523495906679/1764200000000000 : ℝ)*(5257/100000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (8820201128092507357/8821000000000000000 : ℝ)+2*(1523495906679/1764200000000000 : ℝ)*(5257/100000 : ℝ)=(10000002301202413/10000000000000000 : ℝ) by norm_num, show 1+2*(1756732302613/3125000000000000000 : ℝ)=(1562501756732302613/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9314049954353843/12500000000000000000 : ℝ)+(1756732302613/3125000000000000000 : ℝ) ≤ ((8820201128092507357/8821000000000000000 : ℝ)+(1523495906679/1764200000000000 : ℝ)*((22899/100000 : ℝ)+(5257/100000 : ℝ)))^(5003/1024 : ℝ) := by
    rw [show (8820201128092507357/8821000000000000000 : ℝ)+(1523495906679/1764200000000000 : ℝ)*((22899/100000 : ℝ)+(5257/100000 : ℝ))=(2500381449277273/2500000000000000 : ℝ) by norm_num, show 1+(9314049954353843/12500000000000000000 : ℝ)+(1756732302613/3125000000000000000 : ℝ)=(2501864215376712859/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9314049954353843/12500000000000000000 : ℝ) ≤ ((8820201128092507357/8821000000000000000 : ℝ)+2*(1523495906679/1764200000000000 : ℝ)*(22899/100000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (8820201128092507357/8821000000000000000 : ℝ)+2*(1523495906679/1764200000000000 : ℝ)*(22899/100000 : ℝ)=(10003049293015771/10000000000000000 : ℝ) by norm_num, show 1+2*(9314049954353843/12500000000000000000 : ℝ)=(6259314049954353843/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8820201128092507357/8821000000000000000 : ℝ)*(X 1 0+X 2 0)+(1523495906679/1764200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5257/100000 : ℝ)) (hi := (22899/100000 : ℝ)) (c := (8820201128092507357/8821000000000000000 : ℝ)) (alpha := (1523495906679/1764200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8820201128092507357/8821000000000000000 : ℝ)*(X 0 1+X 2 1)+(1523495906679/1764200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5257/100000 : ℝ)) (hi := (22899/100000 : ℝ)) (c := (8820201128092507357/8821000000000000000 : ℝ)) (alpha := (1523495906679/1764200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8820201128092507357/8821000000000000000 : ℝ)*(X 0 2+X 1 2)+(1523495906679/1764200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5257/100000 : ℝ)) (hi := (22899/100000 : ℝ)) (c := (8820201128092507357/8821000000000000000 : ℝ)) (alpha := (1523495906679/1764200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1551924191/10000000000 : ℝ)*X 0 0+(1096141317/2000000000 : ℝ)*X 0 1+(2575398787/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677479097/5000000000 : ℝ)*X 1 0+(-430745027/2500000000 : ℝ)*X 1 1+(5150797631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354958119/10000000000 : ℝ)*X 2 0+(2575398893/5000000000 : ℝ)*X 2 1+(-1722980003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((831661259/2000000000 : ℝ)*X 0 0+(933975117/2500000000 : ℝ)*X 0 1+(230657911/500000000 : ℝ)*X 0 2+(831661259/2000000000 : ℝ)*X 1 0+(933975117/2500000000 : ℝ)*X 1 1+(230657911/500000000 : ℝ)*X 1 2+(831661259/2000000000 : ℝ)*X 2 0+(933975117/2500000000 : ℝ)*X 2 1+(230657911/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-776027891/5000000000 : ℝ)*X 0 0+(2577018651/5000000000 : ℝ)*X 0 1+(5477422507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1316643131/2500000000 : ℝ)*X 1 0+(-349088753/2500000000 : ℝ)*X 1 1+(1369355633/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633286229/5000000000 : ℝ)*X 2 0+(2738711251/5000000000 : ℝ)*X 2 1+(-1396355147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2079327407/5000000000 : ℝ)*X 0 0+(4604542897/10000000000 : ℝ)*X 0 1+(936158203/2500000000 : ℝ)*X 0 2+(2079327407/5000000000 : ℝ)*X 1 0+(4604542897/10000000000 : ℝ)*X 1 1+(936158203/2500000000 : ℝ)*X 1 2+(2079327407/5000000000 : ℝ)*X 2 0+(4604542897/10000000000 : ℝ)*X 2 1+(936158203/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3725008396803293975262792033/441050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68254397/6250000000000 : ℝ)*(base19) + (740909781/100000000000000 : ℝ)*(base23) + (6612453/4000000000000 : ℝ)*(lower2) + (231757243/100000000000000 : ℝ)*(upper3) + (5738993/12500000000000 : ℝ)*(upper5) + (2085541865873577/100000000000000 : ℝ)*(major0) + (2085541865873577/100000000000000 : ℝ)*(major1) + (2085541865873577/100000000000000 : ℝ)*(major2) + (47361720945787/1562500000000 : ℝ)*(sp0) + (3031158695224523/100000000000000 : ℝ)*(sp1) + (1515579523192547/50000000000000 : ℝ)*(sp2) + (56995940174047/5000000000000 : ℝ)*(sp3) + (2411691127/25000000000000 : ℝ)*(sp4) + (4859445549/100000000000000 : ℝ)*(sp7) + (113992366292649/10000000000000 : ℝ)*(f.failure) + (24249278298359/800000000000 : ℝ)*(f.sum) + (205789675669963/88210000000000000000000000000 : ℝ)*base65 + (3481556528756579011/882100000000000000000000000000000 : ℝ)*base68 + (1795744940138720989/882100000000000000000000000000000 : ℝ)*base69 + (4613487892007520989/882100000000000000000000000000000 : ℝ)*base71 + (281780888757907/88210000000000000000000000000 : ℝ)*base74 + (2090546090066220989/882100000000000000000000000000000 : ℝ)*base75 + (5842000272767120989/882100000000000000000000000000000 : ℝ)*base77 + (5551713961691379011/882100000000000000000000000000000 : ℝ)*base80 + (121400697878523/88210000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (183087/25000000000000000000 : ℝ)*base89 + (183087/25000000000000000000 : ℝ)*base91 + (183087/25000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (278633665739689465724473629/110262500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221387/50000000000 : ℝ)*(base19) + (213052093/50000000000000 : ℝ)*(base23) + (2493251/10000000000000 : ℝ)*(upper2) + (59188459/100000000000000 : ℝ)*(upper3) + (100329619/100000000000000 : ℝ)*(upper5) + (1063799909006699/50000000000000 : ℝ)*(major0) + (1063799909006699/50000000000000 : ℝ)*(major1) + (1063799909006699/50000000000000 : ℝ)*(major2) + (4555385433/100000000000000 : ℝ)*(sp1) + (1525156143/50000000000000 : ℝ)*(sp2) + (1546143844112813/50000000000000 : ℝ)*(sp4) + (3092282690066193/100000000000000 : ℝ)*(sp5) + (1546142105904577/50000000000000 : ℝ)*(sp6) + (290727965891933/25000000000000 : ℝ)*(sp7) + (290727965891933/25000000000000 : ℝ)*(f.failure) + (1546143844112813/50000000000000 : ℝ)*(f.sum) + (63706613745441/44105000000000000000000000000 : ℝ)*base65 + (3953395627895910457/441050000000000000000000000000000 : ℝ)*base68 + (2051537796711410457/441050000000000000000000000000000 : ℝ)*base70 + (346193368178210457/441050000000000000000000000000000 : ℝ)*base72 + (76403116183399/44105000000000000000000000000 : ℝ)*base74 + (2912205199984260457/441050000000000000000000000000000 : ℝ)*base76 + (31715282238189543/441050000000000000000000000000000 : ℝ)*base77 + (8800659085880510457/441050000000000000000000000000000 : ℝ)*base80 + (26843761832381/44105000000000000000000000000 : ℝ)*base81 + (597179/62500000000000000000 : ℝ)*base89 + (597179/62500000000000000000 : ℝ)*base91 + (597179/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1672_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5017/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8527/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1672_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1672_s2_0 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1559345809/10000000000 : ℝ)*x 0 + (272177701/500000000 : ℝ)*x 1 + (2591516869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1559345809/10000000000 : ℝ)^5007 ≤ (2417652531731/25000000000000 : ℝ)^3983 := by
    have hnat : (1559345809 : ℕ)^5007*25000000000000^3983 ≤ 2417652531731^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559345809 10000000000 2417652531731 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272177701/500000000 : ℝ)^5007 ≤ (9311290492647/20000000000000 : ℝ)^3983 := by
    have hnat : (272177701 : ℕ)^5007*20000000000000^3983 ≤ 9311290492647^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272177701 500000000 9311290492647 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591516869/5000000000 : ℝ)^5007 ≤ (21886468695903/50000000000000 : ℝ)^3983 := by
    have hnat : (2591516869 : ℕ)^5007*50000000000000^3983 ≤ 21886468695903^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591516869 5000000000 21886468695903 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1559345809/10000000000 : ℝ), (272177701/500000000 : ℝ), (2591516869/5000000000 : ℝ)] ![(2417652531731/25000000000000 : ℝ), (9311290492647/20000000000000 : ℝ), (21886468695903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1559345809/10000000000 : ℝ)|^5007 ≤ (2417652531731/25000000000000 : ℝ)^3983
        have hw : |(-1559345809/10000000000 : ℝ)|=(1559345809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272177701/500000000 : ℝ)|^5007 ≤ (9311290492647/20000000000000 : ℝ)^3983
        have hw : |(272177701/500000000 : ℝ)|=(272177701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591516869/5000000000 : ℝ)|^5007 ≤ (21886468695903/50000000000000 : ℝ)^3983
        have hw : |(2591516869/5000000000 : ℝ)|=(2591516869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s2_1 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345056597/10000000000 : ℝ)*x 0 + (-1693411869/10000000000 : ℝ)*x 1 + (4146427/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345056597/10000000000 : ℝ)^5007 ≤ (1421873203217/3125000000000 : ℝ)^3983 := by
    have hnat : (5345056597 : ℕ)^5007*3125000000000^3983 ≤ 1421873203217^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345056597 10000000000 1421873203217 3125000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1693411869/10000000000 : ℝ)^5007 ≤ (10727119955149/100000000000000 : ℝ)^3983 := by
    have hnat : (1693411869 : ℕ)^5007*100000000000000^3983 ≤ 10727119955149^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693411869 10000000000 10727119955149 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146427/8000000 : ℝ)^5007 ≤ (43772937519207/100000000000000 : ℝ)^3983 := by
    have hnat : (4146427 : ℕ)^5007*100000000000000^3983 ≤ 43772937519207^3983*8000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146427 8000000 43772937519207 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345056597/10000000000 : ℝ), (-1693411869/10000000000 : ℝ), (4146427/8000000 : ℝ)] ![(1421873203217/3125000000000 : ℝ), (10727119955149/100000000000000 : ℝ), (43772937519207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345056597/10000000000 : ℝ)|^5007 ≤ (1421873203217/3125000000000 : ℝ)^3983
        have hw : |(5345056597/10000000000 : ℝ)|=(5345056597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1693411869/10000000000 : ℝ)|^5007 ≤ (10727119955149/100000000000000 : ℝ)^3983
        have hw : |(-1693411869/10000000000 : ℝ)|=(1693411869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146427/8000000 : ℝ)|^5007 ≤ (43772937519207/100000000000000 : ℝ)^3983
        have hw : |(4146427/8000000 : ℝ)|=(4146427/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s2_2 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345056447/10000000000 : ℝ)*x 0 + (2591516893/5000000000 : ℝ)*x 1 + (-67736481/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345056447/10000000000 : ℝ)^5007 ≤ (11374985224447/25000000000000 : ℝ)^3983 := by
    have hnat : (5345056447 : ℕ)^5007*25000000000000^3983 ≤ 11374985224447^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345056447 10000000000 11374985224447 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591516893/5000000000 : ℝ)^5007 ≤ (43772937901407/100000000000000 : ℝ)^3983 := by
    have hnat : (2591516893 : ℕ)^5007*100000000000000^3983 ≤ 43772937901407^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591516893 5000000000 43772937901407 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67736481/400000000 : ℝ)^5007 ≤ (10727121197409/100000000000000 : ℝ)^3983 := by
    have hnat : (67736481 : ℕ)^5007*100000000000000^3983 ≤ 10727121197409^3983*400000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67736481 400000000 10727121197409 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345056447/10000000000 : ℝ), (2591516893/5000000000 : ℝ), (-67736481/400000000 : ℝ)] ![(11374985224447/25000000000000 : ℝ), (43772937901407/100000000000000 : ℝ), (10727121197409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345056447/10000000000 : ℝ)|^5007 ≤ (11374985224447/25000000000000 : ℝ)^3983
        have hw : |(5345056447/10000000000 : ℝ)|=(5345056447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591516893/5000000000 : ℝ)|^5007 ≤ (43772937901407/100000000000000 : ℝ)^3983
        have hw : |(2591516893/5000000000 : ℝ)|=(2591516893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67736481/400000000 : ℝ)|^5007 ≤ (10727121197409/100000000000000 : ℝ)^3983
        have hw : |(-67736481/400000000 : ℝ)|=(67736481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s2_3 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208193279/500000000 : ℝ)*x 0 + (1913806279/5000000000 : ℝ)*x 1 + (452035949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208193279/500000000 : ℝ)^5007 ≤ (33240848566769/100000000000000 : ℝ)^3983 := by
    have hnat : (208193279 : ℕ)^5007*100000000000000^3983 ≤ 33240848566769^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208193279 500000000 33240848566769 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913806279/5000000000 : ℝ)^5007 ≤ (7475527248499/25000000000000 : ℝ)^3983 := by
    have hnat : (1913806279 : ℕ)^5007*25000000000000^3983 ≤ 7475527248499^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913806279 5000000000 7475527248499 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452035949/1000000000 : ℝ)^5007 ≤ (36857042428903/100000000000000 : ℝ)^3983 := by
    have hnat : (452035949 : ℕ)^5007*100000000000000^3983 ≤ 36857042428903^3983*1000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452035949 1000000000 36857042428903 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208193279/500000000 : ℝ), (1913806279/5000000000 : ℝ), (452035949/1000000000 : ℝ)] ![(33240848566769/100000000000000 : ℝ), (7475527248499/25000000000000 : ℝ), (36857042428903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208193279/500000000 : ℝ)|^5007 ≤ (33240848566769/100000000000000 : ℝ)^3983
        have hw : |(208193279/500000000 : ℝ)|=(208193279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1913806279/5000000000 : ℝ)|^5007 ≤ (7475527248499/25000000000000 : ℝ)^3983
        have hw : |(1913806279/5000000000 : ℝ)|=(1913806279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452035949/1000000000 : ℝ)|^5007 ≤ (36857042428903/100000000000000 : ℝ)^3983
        have hw : |(452035949/1000000000 : ℝ)|=(452035949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s2_4 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-97463153/625000000 : ℝ)*x 0 + (2592529509/5000000000 : ℝ)*x 1 + (1360376761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97463153/625000000 : ℝ)^5007 ≤ (38684456253/400000000000 : ℝ)^3983 := by
    have hnat : (97463153 : ℕ)^5007*400000000000^3983 ≤ 38684456253^3983*625000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97463153 625000000 38684456253 400000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592529509/5000000000 : ℝ)^5007 ≤ (42768008039/97656250000 : ℝ)^3983 := by
    have hnat : (2592529509 : ℕ)^5007*97656250000^3983 ≤ 42768008039^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592529509 5000000000 42768008039 97656250000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360376761/2500000000 : ℝ)^5007 ≤ (46534445689233/100000000000000 : ℝ)^3983 := by
    have hnat : (1360376761 : ℕ)^5007*100000000000000^3983 ≤ 46534445689233^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360376761 2500000000 46534445689233 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97463153/625000000 : ℝ), (2592529509/5000000000 : ℝ), (1360376761/2500000000 : ℝ)] ![(38684456253/400000000000 : ℝ), (42768008039/97656250000 : ℝ), (46534445689233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97463153/625000000 : ℝ)|^5007 ≤ (38684456253/400000000000 : ℝ)^3983
        have hw : |(-97463153/625000000 : ℝ)|=(97463153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592529509/5000000000 : ℝ)|^5007 ≤ (42768008039/97656250000 : ℝ)^3983
        have hw : |(2592529509/5000000000 : ℝ)|=(2592529509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360376761/2500000000 : ℝ)|^5007 ≤ (46534445689233/100000000000000 : ℝ)^3983
        have hw : |(1360376761/2500000000 : ℝ)|=(1360376761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s2_5 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275295883/10000000000 : ℝ)*x 0 + (-717469277/5000000000 : ℝ)*x 1 + (43532057/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275295883/10000000000 : ℝ)^5007 ≤ (44754687097281/100000000000000 : ℝ)^3983 := by
    have hnat : (5275295883 : ℕ)^5007*100000000000000^3983 ≤ 44754687097281^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275295883 10000000000 44754687097281 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (717469277/5000000000 : ℝ)^5007 ≤ (4355433165567/50000000000000 : ℝ)^3983 := by
    have hnat : (717469277 : ℕ)^5007*50000000000000^3983 ≤ 4355433165567^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717469277 5000000000 4355433165567 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43532057/80000000 : ℝ)^5007 ≤ (11633611640003/25000000000000 : ℝ)^3983 := by
    have hnat : (43532057 : ℕ)^5007*25000000000000^3983 ≤ 11633611640003^3983*80000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43532057 80000000 11633611640003 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275295883/10000000000 : ℝ), (-717469277/5000000000 : ℝ), (43532057/80000000 : ℝ)] ![(44754687097281/100000000000000 : ℝ), (4355433165567/50000000000000 : ℝ), (11633611640003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275295883/10000000000 : ℝ)|^5007 ≤ (44754687097281/100000000000000 : ℝ)^3983
        have hw : |(5275295883/10000000000 : ℝ)|=(5275295883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-717469277/5000000000 : ℝ)|^5007 ≤ (4355433165567/50000000000000 : ℝ)^3983
        have hw : |(-717469277/5000000000 : ℝ)|=(717469277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43532057/80000000 : ℝ)|^5007 ≤ (11633611640003/25000000000000 : ℝ)^3983
        have hw : |(43532057/80000000 : ℝ)|=(43532057/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s2_6 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275295957/10000000000 : ℝ)*x 0 + (5441507007/10000000000 : ℝ)*x 1 + (-179367327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275295957/10000000000 : ℝ)^5007 ≤ (44754687886487/100000000000000 : ℝ)^3983 := by
    have hnat : (5275295957 : ℕ)^5007*100000000000000^3983 ≤ 44754687886487^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275295957 10000000000 44754687886487 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441507007/10000000000 : ℝ)^5007 ≤ (4653444529147/10000000000000 : ℝ)^3983 := by
    have hnat : (5441507007 : ℕ)^5007*10000000000000^3983 ≤ 4653444529147^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441507007 10000000000 4653444529147 10000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179367327/1250000000 : ℝ)^5007 ≤ (8710866804271/100000000000000 : ℝ)^3983 := by
    have hnat : (179367327 : ℕ)^5007*100000000000000^3983 ≤ 8710866804271^3983*1250000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179367327 1250000000 8710866804271 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275295957/10000000000 : ℝ), (5441507007/10000000000 : ℝ), (-179367327/1250000000 : ℝ)] ![(44754687886487/100000000000000 : ℝ), (4653444529147/10000000000000 : ℝ), (8710866804271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275295957/10000000000 : ℝ)|^5007 ≤ (44754687886487/100000000000000 : ℝ)^3983
        have hw : |(5275295957/10000000000 : ℝ)|=(5275295957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441507007/10000000000 : ℝ)|^5007 ≤ (4653444529147/10000000000000 : ℝ)^3983
        have hw : |(5441507007/10000000000 : ℝ)|=(5441507007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179367327/1250000000 : ℝ)|^5007 ≤ (8710866804271/100000000000000 : ℝ)^3983
        have hw : |(-179367327/1250000000 : ℝ)|=(179367327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s2_7 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041009391/2500000000 : ℝ)*x 0 + (225748711/500000000 : ℝ)*x 1 + (3833055533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041009391/2500000000 : ℝ)^5007 ≤ (33242574535953/100000000000000 : ℝ)^3983 := by
    have hnat : (1041009391 : ℕ)^5007*100000000000000^3983 ≤ 33242574535953^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041009391 2500000000 33242574535953 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225748711/500000000 : ℝ)^5007 ≤ (1840092651003/5000000000000 : ℝ)^3983 := by
    have hnat : (225748711 : ℕ)^5007*5000000000000^3983 ≤ 1840092651003^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225748711 500000000 1840092651003 5000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3833055533/10000000000 : ℝ)^5007 ≤ (7488893106257/25000000000000 : ℝ)^3983 := by
    have hnat : (3833055533 : ℕ)^5007*25000000000000^3983 ≤ 7488893106257^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3833055533 10000000000 7488893106257 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041009391/2500000000 : ℝ), (225748711/500000000 : ℝ), (3833055533/10000000000 : ℝ)] ![(33242574535953/100000000000000 : ℝ), (1840092651003/5000000000000 : ℝ), (7488893106257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041009391/2500000000 : ℝ)|^5007 ≤ (33242574535953/100000000000000 : ℝ)^3983
        have hw : |(1041009391/2500000000 : ℝ)|=(1041009391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225748711/500000000 : ℝ)|^5007 ≤ (1840092651003/5000000000000 : ℝ)^3983
        have hw : |(225748711/500000000 : ℝ)|=(225748711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3833055533/10000000000 : ℝ)|^5007 ≤ (7488893106257/25000000000000 : ℝ)^3983
        have hw : |(3833055533/10000000000 : ℝ)|=(3833055533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1672_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8527/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5017/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1073/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16277/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8527/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5017/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8527/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5017/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8527/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5017/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8527/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5017/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8527/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5017/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8527/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5017/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5017/50000 : ℝ) ^ (5003/1024 : ℝ) ≤ (264539095662391/20000000000000000000 : ℝ) := by
    have hpowers : (5017/50000 : ℝ)^5003 ≤ (264539095662391/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5017 : ℕ)^5003*20000000000000000000^1024 ≤ 264539095662391^1024*50000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5017 50000 264539095662391 20000000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5017/50000 : ℝ)) (X := (264539095662391/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8527/50000 : ℝ) ^ (5003/1024 : ℝ) ≤ (551761211071499/3125000000000000000 : ℝ) := by
    have hpowers : (8527/50000 : ℝ)^5003 ≤ (551761211071499/3125000000000000000 : ℝ)^1024 := by
      have hnat : (8527 : ℕ)^5003*3125000000000000000^1024 ≤ 551761211071499^1024*50000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8527 50000 551761211071499 3125000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8527/50000 : ℝ)) (X := (551761211071499/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000264539095662391/10000000000000000000 : ℝ) ≤ (10000054144550139/10000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (10000264539095662391/10000000000000000000 : ℝ)^1024 ≤ (10000054144550139/10000000000000000 : ℝ)^5003 := by
      have hnat : (10000264539095662391 : ℕ)^1024*10000000000000000^5003 ≤ 10000054144550139^5003*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000264539095662391 10000000000000000000 10000054144550139 10000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054144550139/10000000000000000 : ℝ)) (X := (10000264539095662391/10000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018979054232599923/100000000000000000000 : ℝ) ≤ (2500097107160349/2500000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (100018979054232599923/100000000000000000000 : ℝ)^1024 ≤ (2500097107160349/2500000000000000 : ℝ)^5003 := by
      have hnat : (100018979054232599923 : ℕ)^1024*2500000000000000^5003 ≤ 2500097107160349^5003*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018979054232599923 100000000000000000000 2500097107160349 2500000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500097107160349/2500000000000000 : ℝ)) (X := (100018979054232599923/100000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563051761211071499/1562500000000000000 : ℝ) ≤ (10000722712732653/10000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (1563051761211071499/1562500000000000000 : ℝ)^1024 ≤ (10000722712732653/10000000000000000 : ℝ)^5003 := by
      have hnat : (1563051761211071499 : ℕ)^1024*10000000000000000^5003 ≤ 10000722712732653^5003*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563051761211071499 1562500000000000000 10000722712732653 10000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000722712732653/10000000000000000 : ℝ)) (X := (1563051761211071499/1562500000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(264539095662391/20000000000000000000 : ℝ) ≤ ((731184080016652399/731250000000000000 : ℝ)+2*(111428030419/234000000000000 : ℝ)*(5017/50000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (731184080016652399/731250000000000000 : ℝ)+2*(111428030419/234000000000000 : ℝ)*(5017/50000 : ℝ)=(10000054144550139/10000000000000000 : ℝ) by norm_num, show 1+2*(264539095662391/20000000000000000000 : ℝ)=(10000264539095662391/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(551761211071499/3125000000000000000 : ℝ)+(264539095662391/20000000000000000000 : ℝ) ≤ ((731184080016652399/731250000000000000 : ℝ)+(111428030419/234000000000000 : ℝ)*((8527/50000 : ℝ)+(5017/50000 : ℝ)))^(5003/1024 : ℝ) := by
    rw [show (731184080016652399/731250000000000000 : ℝ)+(111428030419/234000000000000 : ℝ)*((8527/50000 : ℝ)+(5017/50000 : ℝ))=(2500097107160349/2500000000000000 : ℝ) by norm_num, show 1+(551761211071499/3125000000000000000 : ℝ)+(264539095662391/20000000000000000000 : ℝ)=(100018979054232599923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(551761211071499/3125000000000000000 : ℝ) ≤ ((731184080016652399/731250000000000000 : ℝ)+2*(111428030419/234000000000000 : ℝ)*(8527/50000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (731184080016652399/731250000000000000 : ℝ)+2*(111428030419/234000000000000 : ℝ)*(8527/50000 : ℝ)=(10000722712732653/10000000000000000 : ℝ) by norm_num, show 1+2*(551761211071499/3125000000000000000 : ℝ)=(1563051761211071499/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (731184080016652399/731250000000000000 : ℝ)*(X 1 0+X 2 0)+(111428030419/234000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5017/50000 : ℝ)) (hi := (8527/50000 : ℝ)) (c := (731184080016652399/731250000000000000 : ℝ)) (alpha := (111428030419/234000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (731184080016652399/731250000000000000 : ℝ)*(X 0 1+X 2 1)+(111428030419/234000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5017/50000 : ℝ)) (hi := (8527/50000 : ℝ)) (c := (731184080016652399/731250000000000000 : ℝ)) (alpha := (111428030419/234000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (731184080016652399/731250000000000000 : ℝ)*(X 0 2+X 1 2)+(111428030419/234000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5017/50000 : ℝ)) (hi := (8527/50000 : ℝ)) (c := (731184080016652399/731250000000000000 : ℝ)) (alpha := (111428030419/234000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1559345809/10000000000 : ℝ)*X 0 0+(272177701/500000000 : ℝ)*X 0 1+(2591516869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345056597/10000000000 : ℝ)*X 1 0+(-1693411869/10000000000 : ℝ)*X 1 1+(4146427/8000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345056447/10000000000 : ℝ)*X 2 0+(2591516893/5000000000 : ℝ)*X 2 1+(-67736481/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((208193279/500000000 : ℝ)*X 0 0+(1913806279/5000000000 : ℝ)*X 0 1+(452035949/1000000000 : ℝ)*X 0 2+(208193279/500000000 : ℝ)*X 1 0+(1913806279/5000000000 : ℝ)*X 1 1+(452035949/1000000000 : ℝ)*X 1 2+(208193279/500000000 : ℝ)*X 2 0+(1913806279/5000000000 : ℝ)*X 2 1+(452035949/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-97463153/625000000 : ℝ)*X 0 0+(2592529509/5000000000 : ℝ)*X 0 1+(1360376761/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275295883/10000000000 : ℝ)*X 1 0+(-717469277/5000000000 : ℝ)*X 1 1+(43532057/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275295957/10000000000 : ℝ)*X 2 0+(5441507007/10000000000 : ℝ)*X 2 1+(-179367327/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1041009391/2500000000 : ℝ)*X 0 0+(225748711/500000000 : ℝ)*X 0 1+(3833055533/10000000000 : ℝ)*X 0 2+(1041009391/2500000000 : ℝ)*X 1 0+(225748711/500000000 : ℝ)*X 1 1+(3833055533/10000000000 : ℝ)*X 1 2+(1041009391/2500000000 : ℝ)*X 2 0+(225748711/500000000 : ℝ)*X 2 1+(3833055533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50032401663972983083693089/4062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (962947513/50000000000000 : ℝ)*(base19) + (53464991/3125000000000 : ℝ)*(base23) + (11201/19531250000 : ℝ)*(lower2) + (373015851/100000000000000 : ℝ)*(upper3) + (31131293/20000000000000 : ℝ)*(upper5) + (2641033806699721/100000000000000 : ℝ)*(major0) + (2641033806699721/100000000000000 : ℝ)*(major1) + (2641033806699721/100000000000000 : ℝ)*(major2) + (1919249467707191/50000000000000 : ℝ)*(sp0) + (239907415477137/6250000000000 : ℝ)*(sp1) + (1919259431324753/50000000000000 : ℝ)*(sp2) + (288707331296513/20000000000000 : ℝ)*(sp3) + (5409528709/25000000000000 : ℝ)*(sp4) + (1994573077/20000000000000 : ℝ)*(sp7) + (28870932586959/2000000000000 : ℝ)*(f.failure) + (1919260286764609/50000000000000 : ℝ)*(f.sum) + (2196158507299/11700000000000000000000000000 : ℝ)*base65 + (34031181800327509/12187500000000000000000000000000 : ℝ)*base67 + (68245039680640009/12187500000000000000000000000000 : ℝ)*base69 + (50143461352202509/12187500000000000000000000000000 : ℝ)*base71 + (6786093685699/11700000000000000000000000000 : ℝ)*base73 + (57292678211890009/12187500000000000000000000000000 : ℝ)*base75 + (133575423301577509/12187500000000000000000000000000 : ℝ)*base77 + (95776698853422491/12187500000000000000000000000000 : ℝ)*base80 + (23978000174599/11700000000000000000000000000 : ℝ)*base81 + (2617/5000000000000000000 : ℝ)*base89 + (2617/5000000000000000000 : ℝ)*base91 + (2617/5000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29920512997075150860353611/2437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177628997/10000000000000 : ℝ)*(base19) + (993014577/50000000000000 : ℝ)*(base23) + (68895427/25000000000000 : ℝ)*(upper3) + (14423099/20000000000000 : ℝ)*(lower4) + (247371881/100000000000000 : ℝ)*(upper5) + (536587485749057/20000000000000 : ℝ)*(major0) + (536587485749057/20000000000000 : ℝ)*(major1) + (536587485749057/20000000000000 : ℝ)*(major2) + (21887134131/100000000000000 : ℝ)*(sp1) + (4654744163/20000000000000 : ℝ)*(sp2) + (1949711986340467/50000000000000 : ℝ)*(sp4) + (30464064916069/781250000000 : ℝ)*(sp5) + (974849678232741/25000000000000 : ℝ)*(sp6) + (733225237820111/50000000000000 : ℝ)*(sp7) + (733225237820111/50000000000000 : ℝ)*(f.failure) + (1949711986340467/50000000000000 : ℝ)*(f.sum) + (9306687250957/2340000000000000000000000000 : ℝ)*base66 + (15795913422367147/2437500000000000000000000000000 : ℝ)*base68 + (2219788611742147/2437500000000000000000000000000 : ℝ)*base70 + (21515981068679647/2437500000000000000000000000000 : ℝ)*base72 + (1965345105937/2340000000000000000000000000 : ℝ)*base74 + (3700204612117147/2437500000000000000000000000000 : ℝ)*base76 + (10321371580695353/2437500000000000000000000000000 : ℝ)*base77 + (15104534891992147/2437500000000000000000000000000 : ℝ)*base80 + (2515831987703/2340000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (108793/125000000000000000000 : ℝ)*base89 + (108793/125000000000000000000 : ℝ)*base91 + (108793/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1672_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8527/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5017/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1672_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1672_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1672_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1672_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1672_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1672_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
