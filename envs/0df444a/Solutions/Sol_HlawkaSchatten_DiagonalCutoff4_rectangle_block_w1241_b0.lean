-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:19:21.394688+00:00
-- url     : https://prove2.me/submissions/83699469-71eb-4112-8beb-3f455454d55e

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
theorem support_rectangle_w1241_s0_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18608687/100000000 : ℝ)*x 0 + (3015865307/5000000000 : ℝ)*x 1 + (1198216007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18608687/100000000 : ℝ)^4217 ≤ (2170413294641/20000000000000 : ℝ)^3193 := by
    have hnat : (18608687 : ℕ)^4217*20000000000000^3193 ≤ 2170413294641^3193*100000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18608687 100000000 2170413294641 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015865307/5000000000 : ℝ)^4217 ≤ (51289602038557/100000000000000 : ℝ)^3193 := by
    have hnat : (3015865307 : ℕ)^4217*100000000000000^3193 ≤ 51289602038557^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015865307 5000000000 51289602038557 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198216007/2500000000 : ℝ)^4217 ≤ (18929165738283/50000000000000 : ℝ)^3193 := by
    have hnat : (1198216007 : ℕ)^4217*50000000000000^3193 ≤ 18929165738283^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198216007 2500000000 18929165738283 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18608687/100000000 : ℝ), (3015865307/5000000000 : ℝ), (1198216007/2500000000 : ℝ)] ![(2170413294641/20000000000000 : ℝ), (51289602038557/100000000000000 : ℝ), (18929165738283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18608687/100000000 : ℝ)|^4217 ≤ (2170413294641/20000000000000 : ℝ)^3193
        have hw : |(-18608687/100000000 : ℝ)|=(18608687/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015865307/5000000000 : ℝ)|^4217 ≤ (51289602038557/100000000000000 : ℝ)^3193
        have hw : |(3015865307/5000000000 : ℝ)|=(3015865307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198216007/2500000000 : ℝ)|^4217 ≤ (18929165738283/50000000000000 : ℝ)^3193
        have hw : |(1198216007/2500000000 : ℝ)|=(1198216007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s0_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755607913/5000000000 : ℝ)*x 0 + (-513825093/2000000000 : ℝ)*x 1 + (599107997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755607913/5000000000 : ℝ)^4217 ≤ (22763292206283/50000000000000 : ℝ)^3193 := by
    have hnat : (2755607913 : ℕ)^4217*50000000000000^3193 ≤ 22763292206283^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755607913 5000000000 22763292206283 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513825093/2000000000 : ℝ)^4217 ≤ (16615084650283/100000000000000 : ℝ)^3193 := by
    have hnat : (513825093 : ℕ)^4217*100000000000000^3193 ≤ 16615084650283^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513825093 2000000000 16615084650283 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599107997/1250000000 : ℝ)^4217 ≤ (37858330934097/100000000000000 : ℝ)^3193 := by
    have hnat : (599107997 : ℕ)^4217*100000000000000^3193 ≤ 37858330934097^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599107997 1250000000 37858330934097 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755607913/5000000000 : ℝ), (-513825093/2000000000 : ℝ), (599107997/1250000000 : ℝ)] ![(22763292206283/50000000000000 : ℝ), (16615084650283/100000000000000 : ℝ), (37858330934097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755607913/5000000000 : ℝ)|^4217 ≤ (22763292206283/50000000000000 : ℝ)^3193
        have hw : |(2755607913/5000000000 : ℝ)|=(2755607913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513825093/2000000000 : ℝ)|^4217 ≤ (16615084650283/100000000000000 : ℝ)^3193
        have hw : |(-513825093/2000000000 : ℝ)|=(513825093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599107997/1250000000 : ℝ)|^4217 ≤ (37858330934097/100000000000000 : ℝ)^3193
        have hw : |(599107997/1250000000 : ℝ)|=(599107997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s0_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (22044863/40000000 : ℝ)*x 0 + (1198216013/2500000000 : ℝ)*x 1 + (-2569125467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22044863/40000000 : ℝ)^4217 ≤ (4552658358341/10000000000000 : ℝ)^3193 := by
    have hnat : (22044863 : ℕ)^4217*10000000000000^3193 ≤ 4552658358341^3193*40000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22044863 40000000 4552658358341 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198216013/2500000000 : ℝ)^4217 ≤ (4732291465867/12500000000000 : ℝ)^3193 := by
    have hnat : (1198216013 : ℕ)^4217*12500000000000^3193 ≤ 4732291465867^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198216013 2500000000 4732291465867 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569125467/10000000000 : ℝ)^4217 ≤ (8307542333683/50000000000000 : ℝ)^3193 := by
    have hnat : (2569125467 : ℕ)^4217*50000000000000^3193 ≤ 8307542333683^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569125467 10000000000 8307542333683 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22044863/40000000 : ℝ), (1198216013/2500000000 : ℝ), (-2569125467/10000000000 : ℝ)] ![(4552658358341/10000000000000 : ℝ), (4732291465867/12500000000000 : ℝ), (8307542333683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22044863/40000000 : ℝ)|^4217 ≤ (4552658358341/10000000000000 : ℝ)^3193
        have hw : |(22044863/40000000 : ℝ)|=(22044863/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198216013/2500000000 : ℝ)|^4217 ≤ (4732291465867/12500000000000 : ℝ)^3193
        have hw : |(1198216013/2500000000 : ℝ)|=(1198216013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2569125467/10000000000 : ℝ)|^4217 ≤ (8307542333683/50000000000000 : ℝ)^3193
        have hw : |(-2569125467/10000000000 : ℝ)|=(2569125467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s0_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048275031/2500000000 : ℝ)*x 0 + (311692859/1000000000 : ℝ)*x 1 + (2814785741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048275031/2500000000 : ℝ)^4217 ≤ (3966356218517/12500000000000 : ℝ)^3193 := by
    have hnat : (1048275031 : ℕ)^4217*12500000000000^3193 ≤ 3966356218517^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048275031 2500000000 3966356218517 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311692859/1000000000 : ℝ)^4217 ≤ (21446887674259/100000000000000 : ℝ)^3193 := by
    have hnat : (311692859 : ℕ)^4217*100000000000000^3193 ≤ 21446887674259^3193*1000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311692859 1000000000 21446887674259 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814785741/5000000000 : ℝ)^4217 ≤ (4682226255893/10000000000000 : ℝ)^3193 := by
    have hnat : (2814785741 : ℕ)^4217*10000000000000^3193 ≤ 4682226255893^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814785741 5000000000 4682226255893 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048275031/2500000000 : ℝ), (311692859/1000000000 : ℝ), (2814785741/5000000000 : ℝ)] ![(3966356218517/12500000000000 : ℝ), (21446887674259/100000000000000 : ℝ), (4682226255893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048275031/2500000000 : ℝ)|^4217 ≤ (3966356218517/12500000000000 : ℝ)^3193
        have hw : |(1048275031/2500000000 : ℝ)|=(1048275031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311692859/1000000000 : ℝ)|^4217 ≤ (21446887674259/100000000000000 : ℝ)^3193
        have hw : |(311692859/1000000000 : ℝ)|=(311692859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814785741/5000000000 : ℝ)|^4217 ≤ (4682226255893/10000000000000 : ℝ)^3193
        have hw : |(2814785741/5000000000 : ℝ)|=(2814785741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s0_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865729049/10000000000 : ℝ)*x 0 + (4824768201/10000000000 : ℝ)*x 1 + (5998698803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865729049/10000000000 : ℝ)^4217 ≤ (10889516367451/100000000000000 : ℝ)^3193 := by
    have hnat : (1865729049 : ℕ)^4217*100000000000000^3193 ≤ 10889516367451^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865729049 10000000000 10889516367451 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4824768201/10000000000 : ℝ)^4217 ≤ (1909575659367/5000000000000 : ℝ)^3193 := by
    have hnat : (4824768201 : ℕ)^4217*5000000000000^3193 ≤ 1909575659367^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824768201 10000000000 1909575659367 5000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5998698803/10000000000 : ℝ)^4217 ≤ (12729742608801/25000000000000 : ℝ)^3193 := by
    have hnat : (5998698803 : ℕ)^4217*25000000000000^3193 ≤ 12729742608801^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998698803 10000000000 12729742608801 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865729049/10000000000 : ℝ), (4824768201/10000000000 : ℝ), (5998698803/10000000000 : ℝ)] ![(10889516367451/100000000000000 : ℝ), (1909575659367/5000000000000 : ℝ), (12729742608801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865729049/10000000000 : ℝ)|^4217 ≤ (10889516367451/100000000000000 : ℝ)^3193
        have hw : |(-1865729049/10000000000 : ℝ)|=(1865729049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4824768201/10000000000 : ℝ)|^4217 ≤ (1909575659367/5000000000000 : ℝ)^3193
        have hw : |(4824768201/10000000000 : ℝ)|=(4824768201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5998698803/10000000000 : ℝ)|^4217 ≤ (12729742608801/25000000000000 : ℝ)^3193
        have hw : |(5998698803/10000000000 : ℝ)|=(5998698803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s0_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174141907/10000000000 : ℝ)*x 0 + (-170411059/1250000000 : ℝ)*x 1 + (2999350537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174141907/10000000000 : ℝ)^4217 ≤ (327232086127/781250000000 : ℝ)^3193 := by
    have hnat : (5174141907 : ℕ)^4217*781250000000^3193 ≤ 327232086127^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174141907 10000000000 327232086127 781250000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170411059/1250000000 : ℝ)^4217 ≤ (7195297076733/100000000000000 : ℝ)^3193 := by
    have hnat : (170411059 : ℕ)^4217*100000000000000^3193 ≤ 7195297076733^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170411059 1250000000 7195297076733 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2999350537/5000000000 : ℝ)^4217 ≤ (50918995894383/100000000000000 : ℝ)^3193 := by
    have hnat : (2999350537 : ℕ)^4217*100000000000000^3193 ≤ 50918995894383^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999350537 5000000000 50918995894383 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174141907/10000000000 : ℝ), (-170411059/1250000000 : ℝ), (2999350537/5000000000 : ℝ)] ![(327232086127/781250000000 : ℝ), (7195297076733/100000000000000 : ℝ), (50918995894383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174141907/10000000000 : ℝ)|^4217 ≤ (327232086127/781250000000 : ℝ)^3193
        have hw : |(5174141907/10000000000 : ℝ)|=(5174141907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170411059/1250000000 : ℝ)|^4217 ≤ (7195297076733/100000000000000 : ℝ)^3193
        have hw : |(-170411059/1250000000 : ℝ)|=(170411059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2999350537/5000000000 : ℝ)|^4217 ≤ (50918995894383/100000000000000 : ℝ)^3193
        have hw : |(2999350537/5000000000 : ℝ)|=(2999350537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s0_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587071401/5000000000 : ℝ)*x 0 + (23432419/39062500 : ℝ)*x 1 + (-1363290009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587071401/5000000000 : ℝ)^4217 ≤ (41885716593007/100000000000000 : ℝ)^3193 := by
    have hnat : (2587071401 : ℕ)^4217*100000000000000^3193 ≤ 41885716593007^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587071401 5000000000 41885716593007 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23432419/39062500 : ℝ)^4217 ≤ (50918975603271/100000000000000 : ℝ)^3193 := by
    have hnat : (23432419 : ℕ)^4217*100000000000000^3193 ≤ 50918975603271^3193*39062500^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23432419 39062500 50918975603271 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363290009/10000000000 : ℝ)^4217 ≤ (1798826947609/25000000000000 : ℝ)^3193 := by
    have hnat : (1363290009 : ℕ)^4217*25000000000000^3193 ≤ 1798826947609^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363290009 10000000000 1798826947609 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587071401/5000000000 : ℝ), (23432419/39062500 : ℝ), (-1363290009/10000000000 : ℝ)] ![(41885716593007/100000000000000 : ℝ), (50918975603271/100000000000000 : ℝ), (1798826947609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587071401/5000000000 : ℝ)|^4217 ≤ (41885716593007/100000000000000 : ℝ)^3193
        have hw : |(2587071401/5000000000 : ℝ)|=(2587071401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(23432419/39062500 : ℝ)|^4217 ≤ (50918975603271/100000000000000 : ℝ)^3193
        have hw : |(23432419/39062500 : ℝ)|=(23432419/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1363290009/10000000000 : ℝ)|^4217 ≤ (1798826947609/25000000000000 : ℝ)^3193
        have hw : |(-1363290009/10000000000 : ℝ)|=(1363290009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s0_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050739677/2500000000 : ℝ)*x 0 + (2782434659/5000000000 : ℝ)*x 1 + (7959793/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050739677/2500000000 : ℝ)^4217 ≤ (31829416241917/100000000000000 : ℝ)^3193 := by
    have hnat : (1050739677 : ℕ)^4217*100000000000000^3193 ≤ 31829416241917^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050739677 2500000000 31829416241917 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2782434659/5000000000 : ℝ)^4217 ≤ (9222570505147/20000000000000 : ℝ)^3193 := by
    have hnat : (2782434659 : ℕ)^4217*20000000000000^3193 ≤ 9222570505147^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782434659 5000000000 9222570505147 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7959793/25000000 : ℝ)^4217 ≤ (5514432804637/25000000000000 : ℝ)^3193 := by
    have hnat : (7959793 : ℕ)^4217*25000000000000^3193 ≤ 5514432804637^3193*25000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7959793 25000000 5514432804637 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050739677/2500000000 : ℝ), (2782434659/5000000000 : ℝ), (7959793/25000000 : ℝ)] ![(31829416241917/100000000000000 : ℝ), (9222570505147/20000000000000 : ℝ), (5514432804637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050739677/2500000000 : ℝ)|^4217 ≤ (31829416241917/100000000000000 : ℝ)^3193
        have hw : |(1050739677/2500000000 : ℝ)|=(1050739677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2782434659/5000000000 : ℝ)|^4217 ≤ (9222570505147/20000000000000 : ℝ)^3193
        have hw : |(2782434659/5000000000 : ℝ)|=(2782434659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7959793/25000000 : ℝ)|^4217 ≤ (5514432804637/25000000000000 : ℝ)^3193
        have hw : |(7959793/25000000 : ℝ)|=(7959793/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (407/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (343/1250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8433/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8433 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8433*1^2048 ≤ 0^2048*1^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8433/2048 : ℝ) ≤ (1149164147913159961/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8433 ≤ (1149164147913159961/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8433*50000000000000000000^2048 ≤ 1149164147913159961^2048*5^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1149164147913159961 50000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1149164147913159961/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8433 := by
      have hnat : (1 : ℕ)^2048*1^8433 ≤ 1^8433*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51149164147913159961/50000000000000000000 : ℝ) ≤ (10055336943699249/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (51149164147913159961/50000000000000000000 : ℝ)^2048 ≤ (10055336943699249/10000000000000000 : ℝ)^8433 := by
      have hnat : (51149164147913159961 : ℕ)^2048*10000000000000000^8433 ≤ 10055336943699249^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51149164147913159961 50000000000000000000 10055336943699249 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055336943699249/10000000000000000 : ℝ)) (X := (51149164147913159961/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26149164147913159961/25000000000000000000 : ℝ) ≤ (5055336943699249/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (26149164147913159961/25000000000000000000 : ℝ)^2048 ≤ (5055336943699249/5000000000000000 : ℝ)^8433 := by
      have hnat : (26149164147913159961 : ℕ)^2048*5000000000000000^8433 ≤ 5055336943699249^8433*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26149164147913159961 25000000000000000000 5055336943699249 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055336943699249/5000000000000000 : ℝ)) (X := (26149164147913159961/25000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55336943699249/4000000000000000 : ℝ)*(0 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55336943699249/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1149164147913159961/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55336943699249/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55336943699249/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055336943699249/10000000000000000 : ℝ) by norm_num, show 1+(1149164147913159961/50000000000000000000 : ℝ)+(0 : ℝ)=(51149164147913159961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1149164147913159961/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55336943699249/4000000000000000 : ℝ)*(2/5 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55336943699249/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055336943699249/5000000000000000 : ℝ) by norm_num, show 1+2*(1149164147913159961/50000000000000000000 : ℝ)=(26149164147913159961/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55336943699249/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55336943699249/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55336943699249/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55336943699249/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55336943699249/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55336943699249/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-18608687/100000000 : ℝ)*X 0 0+(3015865307/5000000000 : ℝ)*X 0 1+(1198216007/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755607913/5000000000 : ℝ)*X 1 0+(-513825093/2000000000 : ℝ)*X 1 1+(599107997/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((22044863/40000000 : ℝ)*X 2 0+(1198216013/2500000000 : ℝ)*X 2 1+(-2569125467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048275031/2500000000 : ℝ)*X 0 0+(311692859/1000000000 : ℝ)*X 0 1+(2814785741/5000000000 : ℝ)*X 0 2+(1048275031/2500000000 : ℝ)*X 1 0+(311692859/1000000000 : ℝ)*X 1 1+(2814785741/5000000000 : ℝ)*X 1 2+(1048275031/2500000000 : ℝ)*X 2 0+(311692859/1000000000 : ℝ)*X 2 1+(2814785741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1865729049/10000000000 : ℝ)*X 0 0+(4824768201/10000000000 : ℝ)*X 0 1+(5998698803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174141907/10000000000 : ℝ)*X 1 0+(-170411059/1250000000 : ℝ)*X 1 1+(2999350537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587071401/5000000000 : ℝ)*X 2 0+(23432419/39062500 : ℝ)*X 2 1+(-1363290009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050739677/2500000000 : ℝ)*X 0 0+(2782434659/5000000000 : ℝ)*X 0 1+(7959793/25000000 : ℝ)*X 0 2+(1050739677/2500000000 : ℝ)*X 1 0+(2782434659/5000000000 : ℝ)*X 1 1+(7959793/25000000 : ℝ)*X 1 2+(1050739677/2500000000 : ℝ)*X 2 0+(2782434659/5000000000 : ℝ)*X 2 1+(7959793/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137872639611741365601123/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13650873/20000000000000 : ℝ)*(base1) + (1344960731/100000000000000 : ℝ)*(base19) + (622280923/50000000000000 : ℝ)*(base23) + (89267609/100000000000000 : ℝ)*(base24) + (18876869/6250000000000 : ℝ)*(upper3) + (301297042623791/50000000000000 : ℝ)*(major0) + (301297042623791/50000000000000 : ℝ)*(major1) + (301297042623791/50000000000000 : ℝ)*(major2) + (807193979299567/100000000000000 : ℝ)*(sp0) + (807195563166973/100000000000000 : ℝ)*(sp1) + (807195574298249/100000000000000 : ℝ)*(sp2) + (15919547387859/4000000000000 : ℝ)*(sp3) + (1498541251/50000000000000 : ℝ)*(sp4) + (2325586431/100000000000000 : ℝ)*(sp7) + (397991078537271/100000000000000 : ℝ)*(f.failure) + (100899613515963/12500000000000 : ℝ)*(f.sum) + (26958501232959/100000000000000000000000000000 : ℝ)*base65 + (828227086632959/200000000000000000000000000000 : ℝ)*base67 + (592096529832959/200000000000000000000000000000 : ℝ)*base69 + (572554807032959/200000000000000000000000000000 : ℝ)*base71 + (124020869932959/100000000000000000000000000000 : ℝ)*base73 + (829147796632959/200000000000000000000000000000 : ℝ)*base75 + (410933396632959/200000000000000000000000000000 : ℝ)*base77 + (671290705032959/200000000000000000000000000000 : ℝ)*base79 + (158634630467041/100000000000000000000000000000 : ℝ)*base82 + (11785447/10000000000000000000000 : ℝ)*base90 + (11785447/10000000000000000000000 : ℝ)*base92 + (11785447/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (573907446233929801059873/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133876891/100000000000000 : ℝ)*(base1) + (70104371/5000000000000 : ℝ)*(base19) + (1542846339/100000000000000 : ℝ)*(base23) + (321953521/100000000000000 : ℝ)*(upper3) + (13268117/100000000000000 : ℝ)*(upper5) + (635919163497541/100000000000000 : ℝ)*(major0) + (635919163497541/100000000000000 : ℝ)*(major1) + (635919163497541/100000000000000 : ℝ)*(major2) + (116834041/4000000000000 : ℝ)*(sp1) + (2819735397/100000000000000 : ℝ)*(sp2) + (851837210915017/100000000000000 : ℝ)*(sp4) + (851832754099681/100000000000000 : ℝ)*(sp5) + (85183271445639/10000000000000 : ℝ)*(sp6) + (420000924777577/100000000000000 : ℝ)*(sp7) + (420001058654469/100000000000000 : ℝ)*(f.failure) + (425918538519063/50000000000000 : ℝ)*(f.sum) + (320501318446709/200000000000000000000000000000 : ℝ)*base65 + (796549106153291/400000000000000000000000000000 : ℝ)*base68 + (2307214034646709/400000000000000000000000000000 : ℝ)*base69 + (905696121846709/400000000000000000000000000000 : ℝ)*base71 + (830782969246709/200000000000000000000000000000 : ℝ)*base73 + (1808909222553291/400000000000000000000000000000 : ℝ)*base76 + (116125563353291/400000000000000000000000000000 : ℝ)*base78 + (2857097580953291/400000000000000000000000000000 : ℝ)*base80 + (1226641356846709/200000000000000000000000000000 : ℝ)*base81 + (53516267/10000000000000000000000 : ℝ)*base89 + (53516267/10000000000000000000000 : ℝ)*base91 + (53516267/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1241_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (343/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1241_s1_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029175733/5000000000 : ℝ)*x 0 + (5675859021/10000000000 : ℝ)*x 1 + (2511162209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029175733/5000000000 : ℝ)^4217 ≤ (12398358613309/100000000000000 : ℝ)^3193 := by
    have hnat : (1029175733 : ℕ)^4217*100000000000000^3193 ≤ 12398358613309^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029175733 5000000000 12398358613309 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675859021/10000000000 : ℝ)^4217 ≤ (23665689418933/50000000000000 : ℝ)^3193 := by
    have hnat : (5675859021 : ℕ)^4217*50000000000000^3193 ≤ 23665689418933^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675859021 10000000000 23665689418933 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511162209/5000000000 : ℝ)^4217 ≤ (40270262541593/100000000000000 : ℝ)^3193 := by
    have hnat : (2511162209 : ℕ)^4217*100000000000000^3193 ≤ 40270262541593^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511162209 5000000000 40270262541593 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029175733/5000000000 : ℝ), (5675859021/10000000000 : ℝ), (2511162209/5000000000 : ℝ)] ![(12398358613309/100000000000000 : ℝ), (23665689418933/50000000000000 : ℝ), (40270262541593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029175733/5000000000 : ℝ)|^4217 ≤ (12398358613309/100000000000000 : ℝ)^3193
        have hw : |(-1029175733/5000000000 : ℝ)|=(1029175733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675859021/10000000000 : ℝ)|^4217 ≤ (23665689418933/50000000000000 : ℝ)^3193
        have hw : |(5675859021/10000000000 : ℝ)|=(5675859021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511162209/5000000000 : ℝ)|^4217 ≤ (40270262541593/100000000000000 : ℝ)^3193
        have hw : |(2511162209/5000000000 : ℝ)|=(2511162209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s1_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082742641/2000000000 : ℝ)*x 0 + (-1204654813/5000000000 : ℝ)*x 1 + (313895287/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082742641/2000000000 : ℝ)^4217 ≤ (1389558332397/3125000000000 : ℝ)^3193 := by
    have hnat : (1082742641 : ℕ)^4217*3125000000000^3193 ≤ 1389558332397^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082742641 2000000000 1389558332397 3125000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204654813/5000000000 : ℝ)^4217 ≤ (15263868965073/100000000000000 : ℝ)^3193 := by
    have hnat : (1204654813 : ℕ)^4217*100000000000000^3193 ≤ 15263868965073^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204654813 5000000000 15263868965073 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313895287/625000000 : ℝ)^4217 ≤ (10067566096051/25000000000000 : ℝ)^3193 := by
    have hnat : (313895287 : ℕ)^4217*25000000000000^3193 ≤ 10067566096051^3193*625000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313895287 625000000 10067566096051 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082742641/2000000000 : ℝ), (-1204654813/5000000000 : ℝ), (313895287/625000000 : ℝ)] ![(1389558332397/3125000000000 : ℝ), (15263868965073/100000000000000 : ℝ), (10067566096051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082742641/2000000000 : ℝ)|^4217 ≤ (1389558332397/3125000000000 : ℝ)^3193
        have hw : |(1082742641/2000000000 : ℝ)|=(1082742641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1204654813/5000000000 : ℝ)|^4217 ≤ (15263868965073/100000000000000 : ℝ)^3193
        have hw : |(-1204654813/5000000000 : ℝ)|=(1204654813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313895287/625000000 : ℝ)|^4217 ≤ (10067566096051/25000000000000 : ℝ)^3193
        have hw : |(313895287/625000000 : ℝ)|=(313895287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s1_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676714171/1250000000 : ℝ)*x 0 + (5022324477/10000000000 : ℝ)*x 1 + (-2409309559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676714171/1250000000 : ℝ)^4217 ≤ (22232934202437/50000000000000 : ℝ)^3193 := by
    have hnat : (676714171 : ℕ)^4217*50000000000000^3193 ≤ 22232934202437^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676714171 1250000000 22232934202437 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5022324477/10000000000 : ℝ)^4217 ≤ (20135131583193/50000000000000 : ℝ)^3193 := by
    have hnat : (5022324477 : ℕ)^4217*50000000000000^3193 ≤ 20135131583193^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022324477 10000000000 20135131583193 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2409309559/10000000000 : ℝ)^4217 ≤ (610554736179/4000000000000 : ℝ)^3193 := by
    have hnat : (2409309559 : ℕ)^4217*4000000000000^3193 ≤ 610554736179^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409309559 10000000000 610554736179 4000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676714171/1250000000 : ℝ), (5022324477/10000000000 : ℝ), (-2409309559/10000000000 : ℝ)] ![(22232934202437/50000000000000 : ℝ), (20135131583193/50000000000000 : ℝ), (610554736179/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676714171/1250000000 : ℝ)|^4217 ≤ (22232934202437/50000000000000 : ℝ)^3193
        have hw : |(676714171/1250000000 : ℝ)|=(676714171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5022324477/10000000000 : ℝ)|^4217 ≤ (20135131583193/50000000000000 : ℝ)^3193
        have hw : |(5022324477/10000000000 : ℝ)|=(5022324477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2409309559/10000000000 : ℝ)|^4217 ≤ (610554736179/4000000000000 : ℝ)^3193
        have hw : |(-2409309559/10000000000 : ℝ)|=(2409309559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s1_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308941849/10000000000 : ℝ)*x 0 + (3695262351/10000000000 : ℝ)*x 1 + (2510373969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308941849/10000000000 : ℝ)^4217 ≤ (32893700520829/100000000000000 : ℝ)^3193 := by
    have hnat : (4308941849 : ℕ)^4217*100000000000000^3193 ≤ 32893700520829^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308941849 10000000000 32893700520829 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3695262351/10000000000 : ℝ)^4217 ≤ (26852730560319/100000000000000 : ℝ)^3193 := by
    have hnat : (3695262351 : ℕ)^4217*100000000000000^3193 ≤ 26852730560319^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695262351 10000000000 26852730560319 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510373969/5000000000 : ℝ)^4217 ≤ (40253568903857/100000000000000 : ℝ)^3193 := by
    have hnat : (2510373969 : ℕ)^4217*100000000000000^3193 ≤ 40253568903857^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510373969 5000000000 40253568903857 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308941849/10000000000 : ℝ), (3695262351/10000000000 : ℝ), (2510373969/5000000000 : ℝ)] ![(32893700520829/100000000000000 : ℝ), (26852730560319/100000000000000 : ℝ), (40253568903857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308941849/10000000000 : ℝ)|^4217 ≤ (32893700520829/100000000000000 : ℝ)^3193
        have hw : |(4308941849/10000000000 : ℝ)|=(4308941849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3695262351/10000000000 : ℝ)|^4217 ≤ (26852730560319/100000000000000 : ℝ)^3193
        have hw : |(3695262351/10000000000 : ℝ)|=(3695262351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510373969/5000000000 : ℝ)|^4217 ≤ (40253568903857/100000000000000 : ℝ)^3193
        have hw : |(2510373969/5000000000 : ℝ)|=(2510373969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s1_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059029569/10000000000 : ℝ)*x 0 + (1257728219/2500000000 : ℝ)*x 1 + (1133421343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059029569/10000000000 : ℝ)^4217 ≤ (2480750664277/20000000000000 : ℝ)^3193 := by
    have hnat : (2059029569 : ℕ)^4217*20000000000000^3193 ≤ 2480750664277^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059029569 10000000000 2480750664277 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257728219/2500000000 : ℝ)^4217 ≤ (2522577301021/6250000000000 : ℝ)^3193 := by
    have hnat : (1257728219 : ℕ)^4217*6250000000000^3193 ≤ 2522577301021^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257728219 2500000000 2522577301021 6250000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133421343/2000000000 : ℝ)^4217 ≤ (47235009850443/100000000000000 : ℝ)^3193 := by
    have hnat : (1133421343 : ℕ)^4217*100000000000000^3193 ≤ 47235009850443^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133421343 2000000000 47235009850443 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059029569/10000000000 : ℝ), (1257728219/2500000000 : ℝ), (1133421343/2000000000 : ℝ)] ![(2480750664277/20000000000000 : ℝ), (2522577301021/6250000000000 : ℝ), (47235009850443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059029569/10000000000 : ℝ)|^4217 ≤ (2480750664277/20000000000000 : ℝ)^3193
        have hw : |(-2059029569/10000000000 : ℝ)|=(2059029569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1257728219/2500000000 : ℝ)|^4217 ≤ (2522577301021/6250000000000 : ℝ)^3193
        have hw : |(1257728219/2500000000 : ℝ)|=(1257728219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133421343/2000000000 : ℝ)|^4217 ≤ (47235009850443/100000000000000 : ℝ)^3193
        have hw : |(1133421343/2000000000 : ℝ)|=(1133421343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s1_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311337901/2500000000 : ℝ)*x 0 + (-1764526931/10000000000 : ℝ)*x 1 + (2833553417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311337901/2500000000 : ℝ)^4217 ≤ (21324354565379/50000000000000 : ℝ)^3193 := by
    have hnat : (1311337901 : ℕ)^4217*50000000000000^3193 ≤ 21324354565379^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311337901 2500000000 21324354565379 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1764526931/10000000000 : ℝ)^4217 ≤ (10116279689577/100000000000000 : ℝ)^3193 := by
    have hnat : (1764526931 : ℕ)^4217*100000000000000^3193 ≤ 10116279689577^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764526931 10000000000 10116279689577 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2833553417/5000000000 : ℝ)^4217 ≤ (5904376395049/12500000000000 : ℝ)^3193 := by
    have hnat : (2833553417 : ℕ)^4217*12500000000000^3193 ≤ 5904376395049^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833553417 5000000000 5904376395049 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311337901/2500000000 : ℝ), (-1764526931/10000000000 : ℝ), (2833553417/5000000000 : ℝ)] ![(21324354565379/50000000000000 : ℝ), (10116279689577/100000000000000 : ℝ), (5904376395049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311337901/2500000000 : ℝ)|^4217 ≤ (21324354565379/50000000000000 : ℝ)^3193
        have hw : |(1311337901/2500000000 : ℝ)|=(1311337901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1764526931/10000000000 : ℝ)|^4217 ≤ (10116279689577/100000000000000 : ℝ)^3193
        have hw : |(-1764526931/10000000000 : ℝ)|=(1764526931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2833553417/5000000000 : ℝ)|^4217 ≤ (5904376395049/12500000000000 : ℝ)^3193
        have hw : |(2833553417/5000000000 : ℝ)|=(2833553417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s1_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245351973/10000000000 : ℝ)*x 0 + (708388451/1250000000 : ℝ)*x 1 + (-1764525283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245351973/10000000000 : ℝ)^4217 ≤ (8529742618639/20000000000000 : ℝ)^3193 := by
    have hnat : (5245351973 : ℕ)^4217*20000000000000^3193 ≤ 8529742618639^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245351973 10000000000 8529742618639 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708388451/1250000000 : ℝ)^4217 ≤ (23617509840281/50000000000000 : ℝ)^3193 := by
    have hnat : (708388451 : ℕ)^4217*50000000000000^3193 ≤ 23617509840281^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708388451 1250000000 23617509840281 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1764525283/10000000000 : ℝ)^4217 ≤ (10116267211307/100000000000000 : ℝ)^3193 := by
    have hnat : (1764525283 : ℕ)^4217*100000000000000^3193 ≤ 10116267211307^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764525283 10000000000 10116267211307 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245351973/10000000000 : ℝ), (708388451/1250000000 : ℝ), (-1764525283/10000000000 : ℝ)] ![(8529742618639/20000000000000 : ℝ), (23617509840281/50000000000000 : ℝ), (10116267211307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245351973/10000000000 : ℝ)|^4217 ≤ (8529742618639/20000000000000 : ℝ)^3193
        have hw : |(5245351973/10000000000 : ℝ)|=(5245351973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708388451/1250000000 : ℝ)|^4217 ≤ (23617509840281/50000000000000 : ℝ)^3193
        have hw : |(708388451/1250000000 : ℝ)|=(708388451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1764525283/10000000000 : ℝ)|^4217 ≤ (10116267211307/100000000000000 : ℝ)^3193
        have hw : |(-1764525283/10000000000 : ℝ)|=(1764525283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s1_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310315563/10000000000 : ℝ)*x 0 + (5003329761/10000000000 : ℝ)*x 1 + (464126533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310315563/10000000000 : ℝ)^4217 ≤ (32907551016217/100000000000000 : ℝ)^3193 := by
    have hnat : (4310315563 : ℕ)^4217*100000000000000^3193 ≤ 32907551016217^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310315563 10000000000 32907551016217 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003329761/10000000000 : ℝ)^4217 ≤ (40069236578727/100000000000000 : ℝ)^3193 := by
    have hnat : (5003329761 : ℕ)^4217*100000000000000^3193 ≤ 40069236578727^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003329761 10000000000 40069236578727 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464126533/1250000000 : ℝ)^4217 ≤ (5404642478521/20000000000000 : ℝ)^3193 := by
    have hnat : (464126533 : ℕ)^4217*20000000000000^3193 ≤ 5404642478521^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464126533 1250000000 5404642478521 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310315563/10000000000 : ℝ), (5003329761/10000000000 : ℝ), (464126533/1250000000 : ℝ)] ![(32907551016217/100000000000000 : ℝ), (40069236578727/100000000000000 : ℝ), (5404642478521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310315563/10000000000 : ℝ)|^4217 ≤ (32907551016217/100000000000000 : ℝ)^3193
        have hw : |(4310315563/10000000000 : ℝ)|=(4310315563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003329761/10000000000 : ℝ)|^4217 ≤ (40069236578727/100000000000000 : ℝ)^3193
        have hw : |(5003329761/10000000000 : ℝ)|=(5003329761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464126533/1250000000 : ℝ)|^4217 ≤ (5404642478521/20000000000000 : ℝ)^3193
        have hw : |(464126533/1250000000 : ℝ)|=(464126533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3093/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (343/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (343/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (343/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (343/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (343/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (343/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (407/50000 : ℝ) ^ (8433/2048 : ℝ) ≤ (12462314829/5000000000000000000 : ℝ) := by
    have hpowers : (407/50000 : ℝ)^8433 ≤ (12462314829/5000000000000000000 : ℝ)^2048 := by
      have hnat : (407 : ℕ)^8433*5000000000000000000^2048 ≤ 12462314829^2048*50000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        407 50000 12462314829 5000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (407/50000 : ℝ)) (X := (12462314829/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (343/1250 : ℝ) ^ (8433/2048 : ℝ) ≤ (486909041567302903/100000000000000000000 : ℝ) := by
    have hpowers : (343/1250 : ℝ)^8433 ≤ (486909041567302903/100000000000000000000 : ℝ)^2048 := by
      have hnat : (343 : ℕ)^8433*100000000000000000000^2048 ≤ 486909041567302903^2048*1250^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        343 1250 486909041567302903 100000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (343/1250 : ℝ)) (X := (486909041567302903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000012462314829/2500000000000000000 : ℝ) ≤ (2000000002421233/2000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (2500000012462314829/2500000000000000000 : ℝ)^2048 ≤ (2000000002421233/2000000000000000 : ℝ)^8433 := by
      have hnat : (2500000012462314829 : ℕ)^2048*2000000000000000^8433 ≤ 2000000002421233^8433*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000012462314829 2500000000000000000 2000000002421233 2000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000002421233/2000000000000000 : ℝ)) (X := (2500000012462314829/2500000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100486909290813599483/100000000000000000000 : ℝ) ≤ (500590156129423/500000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (100486909290813599483/100000000000000000000 : ℝ)^2048 ≤ (500590156129423/500000000000000 : ℝ)^8433 := by
      have hnat : (100486909290813599483 : ℕ)^2048*500000000000000^8433 ≤ 500590156129423^8433*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100486909290813599483 100000000000000000000 500590156129423 500000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500590156129423/500000000000000 : ℝ)) (X := (100486909290813599483/100000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50486909041567302903/50000000000000000000 : ℝ) ≤ (2004721246614151/2000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (50486909041567302903/50000000000000000000 : ℝ)^2048 ≤ (2004721246614151/2000000000000000 : ℝ)^8433 := by
      have hnat : (50486909041567302903 : ℕ)^2048*2000000000000000^8433 ≤ 2004721246614151^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50486909041567302903 50000000000000000000 2004721246614151 2000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004721246614151/2000000000000000 : ℝ)) (X := (50486909041567302903/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12462314829/5000000000000000000 : ℝ) ≤ ((26624078485847357303/26626000000000000000 : ℝ)+2*(2360622096459/532520000000000 : ℝ)*(407/50000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (26624078485847357303/26626000000000000000 : ℝ)+2*(2360622096459/532520000000000 : ℝ)*(407/50000 : ℝ)=(2000000002421233/2000000000000000 : ℝ) by norm_num, show 1+2*(12462314829/5000000000000000000 : ℝ)=(2500000012462314829/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(486909041567302903/100000000000000000000 : ℝ)+(12462314829/5000000000000000000 : ℝ) ≤ ((26624078485847357303/26626000000000000000 : ℝ)+(2360622096459/532520000000000 : ℝ)*((343/1250 : ℝ)+(407/50000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (26624078485847357303/26626000000000000000 : ℝ)+(2360622096459/532520000000000 : ℝ)*((343/1250 : ℝ)+(407/50000 : ℝ))=(500590156129423/500000000000000 : ℝ) by norm_num, show 1+(486909041567302903/100000000000000000000 : ℝ)+(12462314829/5000000000000000000 : ℝ)=(100486909290813599483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(486909041567302903/100000000000000000000 : ℝ) ≤ ((26624078485847357303/26626000000000000000 : ℝ)+2*(2360622096459/532520000000000 : ℝ)*(343/1250 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (26624078485847357303/26626000000000000000 : ℝ)+2*(2360622096459/532520000000000 : ℝ)*(343/1250 : ℝ)=(2004721246614151/2000000000000000 : ℝ) by norm_num, show 1+2*(486909041567302903/100000000000000000000 : ℝ)=(50486909041567302903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26624078485847357303/26626000000000000000 : ℝ)*(X 1 0+X 2 0)+(2360622096459/532520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (407/50000 : ℝ)) (hi := (343/1250 : ℝ)) (c := (26624078485847357303/26626000000000000000 : ℝ)) (alpha := (2360622096459/532520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26624078485847357303/26626000000000000000 : ℝ)*(X 0 1+X 2 1)+(2360622096459/532520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (407/50000 : ℝ)) (hi := (343/1250 : ℝ)) (c := (26624078485847357303/26626000000000000000 : ℝ)) (alpha := (2360622096459/532520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26624078485847357303/26626000000000000000 : ℝ)*(X 0 2+X 1 2)+(2360622096459/532520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (407/50000 : ℝ)) (hi := (343/1250 : ℝ)) (c := (26624078485847357303/26626000000000000000 : ℝ)) (alpha := (2360622096459/532520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1029175733/5000000000 : ℝ)*X 0 0+(5675859021/10000000000 : ℝ)*X 0 1+(2511162209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1082742641/2000000000 : ℝ)*X 1 0+(-1204654813/5000000000 : ℝ)*X 1 1+(313895287/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676714171/1250000000 : ℝ)*X 2 0+(5022324477/10000000000 : ℝ)*X 2 1+(-2409309559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308941849/10000000000 : ℝ)*X 0 0+(3695262351/10000000000 : ℝ)*X 0 1+(2510373969/5000000000 : ℝ)*X 0 2+(4308941849/10000000000 : ℝ)*X 1 0+(3695262351/10000000000 : ℝ)*X 1 1+(2510373969/5000000000 : ℝ)*X 1 2+(4308941849/10000000000 : ℝ)*X 2 0+(3695262351/10000000000 : ℝ)*X 2 1+(2510373969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2059029569/10000000000 : ℝ)*X 0 0+(1257728219/2500000000 : ℝ)*X 0 1+(1133421343/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1311337901/2500000000 : ℝ)*X 1 0+(-1764526931/10000000000 : ℝ)*X 1 1+(2833553417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245351973/10000000000 : ℝ)*X 2 0+(708388451/1250000000 : ℝ)*X 2 1+(-1764525283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310315563/10000000000 : ℝ)*X 0 0+(5003329761/10000000000 : ℝ)*X 0 1+(464126533/1250000000 : ℝ)*X 0 2+(4310315563/10000000000 : ℝ)*X 1 0+(5003329761/10000000000 : ℝ)*X 1 1+(464126533/1250000000 : ℝ)*X 1 2+(4310315563/10000000000 : ℝ)*X 2 0+(5003329761/10000000000 : ℝ)*X 2 1+(464126533/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (272371963284807229074564231/83206250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15956891/50000000000000 : ℝ)*(base1) + (378946009/50000000000000 : ℝ)*(base19) + (803962851/100000000000000 : ℝ)*(base23) + (79852319/100000000000000 : ℝ)*(upper3) + (116632557/100000000000000 : ℝ)*(upper5) + (71393597566653/6250000000000 : ℝ)*(major0) + (71393597566653/6250000000000 : ℝ)*(major1) + (71393597566653/6250000000000 : ℝ)*(major2) + (1530145029693161/100000000000000 : ℝ)*(sp0) + (1530149016665467/100000000000000 : ℝ)*(sp1) + (1530148970594633/100000000000000 : ℝ)*(sp2) + (377221438587871/50000000000000 : ℝ)*(sp3) + (2388389053/50000000000000 : ℝ)*(sp4) + (465874139/20000000000000 : ℝ)*(sp7) + (37722261923011/5000000000000 : ℝ)*(f.failure) + (382537443639371/25000000000000 : ℝ)*(f.sum) + (40258726376177/13313000000000000000000000000 : ℝ)*base65 + (582141057273108141/166412500000000000000000000000000 : ℝ)*base68 + (179226272446483141/166412500000000000000000000000000 : ℝ)*base70 + (261872446866258141/166412500000000000000000000000000 : ℝ)*base72 + (23654152466381/13313000000000000000000000000 : ℝ)*base73 + (950677575030083141/166412500000000000000000000000000 : ℝ)*base76 + (231212975471470641/166412500000000000000000000000000 : ℝ)*base78 + (343602667915008141/166412500000000000000000000000000 : ℝ)*base80 + (58356235841939/13313000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2887373/500000000000000000000 : ℝ)*base89 + (2887373/500000000000000000000 : ℝ)*base91 + (2887373/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2188119484305239015952353391/665650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67702803/5000000000000 : ℝ)*(base19) + (925415633/50000000000000 : ℝ)*(base23) + (103645903/100000000000000 : ℝ)*(upper2) + (112323413/50000000000000 : ℝ)*(upper3) + (83264927/100000000000000 : ℝ)*(upper5) + (1173425212746699/100000000000000 : ℝ)*(major0) + (1173425212746699/100000000000000 : ℝ)*(major1) + (1173425212746699/100000000000000 : ℝ)*(major2) + (1181038019/20000000000000 : ℝ)*(sp1) + (2356238749/20000000000000 : ℝ)*(sp2) + (1571846416218899/100000000000000 : ℝ)*(sp4) + (314367831394549/20000000000000 : ℝ)*(sp5) + (1571832784193887/100000000000000 : ℝ)*(sp6) + (775003899701419/100000000000000 : ℝ)*(sp7) + (775003899701419/100000000000000 : ℝ)*(f.failure) + (1571846416218899/100000000000000 : ℝ)*(f.sum) + (67107198389/1065040000000000000000000000 : ℝ)*base65 + (6394587121146957203/2662600000000000000000000000000000 : ℝ)*base68 + (791771180073757203/2662600000000000000000000000000000 : ℝ)*base70 + (16888817560806357203/2662600000000000000000000000000000 : ℝ)*base72 + (33376019582203/26626000000000000000000000000 : ℝ)*base74 + (24919583495014757203/2662600000000000000000000000000000 : ℝ)*base76 + (5140720122131957203/2662600000000000000000000000000000 : ℝ)*base78 + (23575784557076842797/2662600000000000000000000000000000 : ℝ)*base79 + (31262100837201/26626000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (33609883/10000000000000000000000 : ℝ)*base90 + (33609883/10000000000000000000000 : ℝ)*base92 + (33609883/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1241_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (343/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3093/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1241_s2_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-421289047/2000000000 : ℝ)*x 0 + (686619959/1250000000 : ℝ)*x 1 + (5174553231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421289047/2000000000 : ℝ)^4217 ≤ (319559463519/2500000000000 : ℝ)^3193 := by
    have hnat : (421289047 : ℕ)^4217*2500000000000^3193 ≤ 319559463519^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421289047 2000000000 319559463519 2500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686619959/1250000000 : ℝ)^4217 ≤ (22663758377829/50000000000000 : ℝ)^3193 := by
    have hnat : (686619959 : ℕ)^4217*50000000000000^3193 ≤ 22663758377829^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686619959 1250000000 22663758377829 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174553231/10000000000 : ℝ)^4217 ≤ (2094505234281/5000000000000 : ℝ)^3193 := by
    have hnat : (5174553231 : ℕ)^4217*5000000000000^3193 ≤ 2094505234281^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174553231 10000000000 2094505234281 5000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421289047/2000000000 : ℝ), (686619959/1250000000 : ℝ), (5174553231/10000000000 : ℝ)] ![(319559463519/2500000000000 : ℝ), (22663758377829/50000000000000 : ℝ), (2094505234281/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421289047/2000000000 : ℝ)|^4217 ≤ (319559463519/2500000000000 : ℝ)^3193
        have hw : |(-421289047/2000000000 : ℝ)|=(421289047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686619959/1250000000 : ℝ)|^4217 ≤ (22663758377829/50000000000000 : ℝ)^3193
        have hw : |(686619959/1250000000 : ℝ)|=(686619959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174553231/10000000000 : ℝ)|^4217 ≤ (2094505234281/5000000000000 : ℝ)^3193
        have hw : |(5174553231/10000000000 : ℝ)|=(5174553231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s2_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342431717/2500000000 : ℝ)*x 0 + (-1135691611/5000000000 : ℝ)*x 1 + (5174553233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342431717/2500000000 : ℝ)^4217 ≤ (549866755763/1250000000000 : ℝ)^3193 := by
    have hnat : (1342431717 : ℕ)^4217*1250000000000^3193 ≤ 549866755763^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342431717 2500000000 549866755763 1250000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135691611/5000000000 : ℝ)^4217 ≤ (14120554820557/100000000000000 : ℝ)^3193 := by
    have hnat : (1135691611 : ℕ)^4217*100000000000000^3193 ≤ 14120554820557^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135691611 5000000000 14120554820557 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174553233/10000000000 : ℝ)^4217 ≤ (41890104707003/100000000000000 : ℝ)^3193 := by
    have hnat : (5174553233 : ℕ)^4217*100000000000000^3193 ≤ 41890104707003^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174553233 10000000000 41890104707003 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342431717/2500000000 : ℝ), (-1135691611/5000000000 : ℝ), (5174553233/10000000000 : ℝ)] ![(549866755763/1250000000000 : ℝ), (14120554820557/100000000000000 : ℝ), (41890104707003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342431717/2500000000 : ℝ)|^4217 ≤ (549866755763/1250000000000 : ℝ)^3193
        have hw : |(1342431717/2500000000 : ℝ)|=(1342431717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135691611/5000000000 : ℝ)|^4217 ≤ (14120554820557/100000000000000 : ℝ)^3193
        have hw : |(-1135691611/5000000000 : ℝ)|=(1135691611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174553233/10000000000 : ℝ)|^4217 ≤ (41890104707003/100000000000000 : ℝ)^3193
        have hw : |(5174553233/10000000000 : ℝ)|=(5174553233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s2_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073945343/2000000000 : ℝ)*x 0 + (1293638339/2500000000 : ℝ)*x 1 + (-2271383263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073945343/2000000000 : ℝ)^4217 ≤ (10997334701421/25000000000000 : ℝ)^3193 := by
    have hnat : (1073945343 : ℕ)^4217*25000000000000^3193 ≤ 10997334701421^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073945343 2000000000 10997334701421 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293638339/2500000000 : ℝ)^4217 ≤ (5236263252759/12500000000000 : ℝ)^3193 := by
    have hnat : (1293638339 : ℕ)^4217*12500000000000^3193 ≤ 5236263252759^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293638339 2500000000 5236263252759 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271383263/10000000000 : ℝ)^4217 ≤ (2824111031437/20000000000000 : ℝ)^3193 := by
    have hnat : (2271383263 : ℕ)^4217*20000000000000^3193 ≤ 2824111031437^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271383263 10000000000 2824111031437 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073945343/2000000000 : ℝ), (1293638339/2500000000 : ℝ), (-2271383263/10000000000 : ℝ)] ![(10997334701421/25000000000000 : ℝ), (5236263252759/12500000000000 : ℝ), (2824111031437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073945343/2000000000 : ℝ)|^4217 ≤ (10997334701421/25000000000000 : ℝ)^3193
        have hw : |(1073945343/2000000000 : ℝ)|=(1073945343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293638339/2500000000 : ℝ)|^4217 ≤ (5236263252759/12500000000000 : ℝ)^3193
        have hw : |(1293638339/2500000000 : ℝ)|=(1293638339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2271383263/10000000000 : ℝ)|^4217 ≤ (2824111031437/20000000000000 : ℝ)^3193
        have hw : |(-2271383263/10000000000 : ℝ)|=(2271383263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s2_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171080137/5000000000 : ℝ)*x 0 + (4030898727/10000000000 : ℝ)*x 1 + (935336787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171080137/5000000000 : ℝ)^4217 ≤ (33229022035667/100000000000000 : ℝ)^3193 := by
    have hnat : (2171080137 : ℕ)^4217*100000000000000^3193 ≤ 33229022035667^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171080137 5000000000 33229022035667 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030898727/10000000000 : ℝ)^4217 ≤ (30119909776263/100000000000000 : ℝ)^3193 := by
    have hnat : (4030898727 : ℕ)^4217*100000000000000^3193 ≤ 30119909776263^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030898727 10000000000 30119909776263 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935336787/2000000000 : ℝ)^4217 ≤ (7330213634197/20000000000000 : ℝ)^3193 := by
    have hnat : (935336787 : ℕ)^4217*20000000000000^3193 ≤ 7330213634197^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935336787 2000000000 7330213634197 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171080137/5000000000 : ℝ), (4030898727/10000000000 : ℝ), (935336787/2000000000 : ℝ)] ![(33229022035667/100000000000000 : ℝ), (30119909776263/100000000000000 : ℝ), (7330213634197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171080137/5000000000 : ℝ)|^4217 ≤ (33229022035667/100000000000000 : ℝ)^3193
        have hw : |(2171080137/5000000000 : ℝ)|=(2171080137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030898727/10000000000 : ℝ)|^4217 ≤ (30119909776263/100000000000000 : ℝ)^3193
        have hw : |(4030898727/10000000000 : ℝ)|=(4030898727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(935336787/2000000000 : ℝ)|^4217 ≤ (7330213634197/20000000000000 : ℝ)^3193
        have hw : |(935336787/2000000000 : ℝ)|=(935336787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s2_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053261931/5000000000 : ℝ)*x 0 + (2588300767/5000000000 : ℝ)*x 1 + (5490892149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053261931/5000000000 : ℝ)^4217 ≤ (12783008685753/100000000000000 : ℝ)^3193 := by
    have hnat : (1053261931 : ℕ)^4217*100000000000000^3193 ≤ 12783008685753^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053261931 5000000000 12783008685753 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588300767/5000000000 : ℝ)^4217 ≤ (8382401148097/20000000000000 : ℝ)^3193 := by
    have hnat : (2588300767 : ℕ)^4217*20000000000000^3193 ≤ 8382401148097^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588300767 5000000000 8382401148097 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490892149/10000000000 : ℝ)^4217 ≤ (4530498555509/10000000000000 : ℝ)^3193 := by
    have hnat : (5490892149 : ℕ)^4217*10000000000000^3193 ≤ 4530498555509^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490892149 10000000000 4530498555509 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053261931/5000000000 : ℝ), (2588300767/5000000000 : ℝ), (5490892149/10000000000 : ℝ)] ![(12783008685753/100000000000000 : ℝ), (8382401148097/20000000000000 : ℝ), (4530498555509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053261931/5000000000 : ℝ)|^4217 ≤ (12783008685753/100000000000000 : ℝ)^3193
        have hw : |(-1053261931/5000000000 : ℝ)|=(1053261931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588300767/5000000000 : ℝ)|^4217 ≤ (8382401148097/20000000000000 : ℝ)^3193
        have hw : |(2588300767/5000000000 : ℝ)|=(2588300767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490892149/10000000000 : ℝ)|^4217 ≤ (4530498555509/10000000000000 : ℝ)^3193
        have hw : |(5490892149/10000000000 : ℝ)|=(5490892149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s2_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644209691/5000000000 : ℝ)*x 0 + (-244380511/1250000000 : ℝ)*x 1 + (5490892193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644209691/5000000000 : ℝ)^4217 ≤ (1347243502333/3125000000000 : ℝ)^3193 := by
    have hnat : (2644209691 : ℕ)^4217*3125000000000^3193 ≤ 1347243502333^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644209691 5000000000 1347243502333 3125000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244380511/1250000000 : ℝ)^4217 ≤ (5791610935839/50000000000000 : ℝ)^3193 := by
    have hnat : (244380511 : ℕ)^4217*50000000000000^3193 ≤ 5791610935839^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244380511 1250000000 5791610935839 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490892193/10000000000 : ℝ)^4217 ≤ (45304986034559/100000000000000 : ℝ)^3193 := by
    have hnat : (5490892193 : ℕ)^4217*100000000000000^3193 ≤ 45304986034559^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490892193 10000000000 45304986034559 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644209691/5000000000 : ℝ), (-244380511/1250000000 : ℝ), (5490892193/10000000000 : ℝ)] ![(1347243502333/3125000000000 : ℝ), (5791610935839/50000000000000 : ℝ), (45304986034559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644209691/5000000000 : ℝ)|^4217 ≤ (1347243502333/3125000000000 : ℝ)^3193
        have hw : |(2644209691/5000000000 : ℝ)|=(2644209691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244380511/1250000000 : ℝ)|^4217 ≤ (5791610935839/50000000000000 : ℝ)^3193
        have hw : |(-244380511/1250000000 : ℝ)|=(244380511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490892193/10000000000 : ℝ)|^4217 ≤ (45304986034559/100000000000000 : ℝ)^3193
        have hw : |(5490892193/10000000000 : ℝ)|=(5490892193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s2_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288419549/10000000000 : ℝ)*x 0 + (5490892273/10000000000 : ℝ)*x 1 + (-488760937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288419549/10000000000 : ℝ)^4217 ≤ (43111793872663/100000000000000 : ℝ)^3193 := by
    have hnat : (5288419549 : ℕ)^4217*100000000000000^3193 ≤ 43111793872663^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288419549 10000000000 43111793872663 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490892273/10000000000 : ℝ)^4217 ≤ (566312336329/1250000000000 : ℝ)^3193 := by
    have hnat : (5490892273 : ℕ)^4217*1250000000000^3193 ≤ 566312336329^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490892273 10000000000 566312336329 1250000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488760937/2500000000 : ℝ)^4217 ≤ (579160960561/5000000000000 : ℝ)^3193 := by
    have hnat : (488760937 : ℕ)^4217*5000000000000^3193 ≤ 579160960561^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488760937 2500000000 579160960561 5000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288419549/10000000000 : ℝ), (5490892273/10000000000 : ℝ), (-488760937/2500000000 : ℝ)] ![(43111793872663/100000000000000 : ℝ), (566312336329/1250000000000 : ℝ), (579160960561/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288419549/10000000000 : ℝ)|^4217 ≤ (43111793872663/100000000000000 : ℝ)^3193
        have hw : |(5288419549/10000000000 : ℝ)|=(5288419549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490892273/10000000000 : ℝ)|^4217 ≤ (566312336329/1250000000000 : ℝ)^3193
        have hw : |(5490892273/10000000000 : ℝ)|=(5490892273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488760937/2500000000 : ℝ)|^4217 ≤ (579160960561/5000000000000 : ℝ)^3193
        have hw : |(-488760937/2500000000 : ℝ)|=(488760937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s2_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342319209/10000000000 : ℝ)*x 0 + (4672529863/10000000000 : ℝ)*x 1 + (4035091467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342319209/10000000000 : ℝ)^4217 ≤ (4153828547427/12500000000000 : ℝ)^3193 := by
    have hnat : (4342319209 : ℕ)^4217*12500000000000^3193 ≤ 4153828547427^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342319209 10000000000 4153828547427 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4672529863/10000000000 : ℝ)^4217 ≤ (7321615673807/20000000000000 : ℝ)^3193 := by
    have hnat : (4672529863 : ℕ)^4217*20000000000000^3193 ≤ 7321615673807^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4672529863 10000000000 7321615673807 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035091467/10000000000 : ℝ)^4217 ≤ (30161293237007/100000000000000 : ℝ)^3193 := by
    have hnat : (4035091467 : ℕ)^4217*100000000000000^3193 ≤ 30161293237007^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035091467 10000000000 30161293237007 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342319209/10000000000 : ℝ), (4672529863/10000000000 : ℝ), (4035091467/10000000000 : ℝ)] ![(4153828547427/12500000000000 : ℝ), (7321615673807/20000000000000 : ℝ), (30161293237007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342319209/10000000000 : ℝ)|^4217 ≤ (4153828547427/12500000000000 : ℝ)^3193
        have hw : |(4342319209/10000000000 : ℝ)|=(4342319209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4672529863/10000000000 : ℝ)|^4217 ≤ (7321615673807/20000000000000 : ℝ)^3193
        have hw : |(4672529863/10000000000 : ℝ)|=(4672529863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035091467/10000000000 : ℝ)|^4217 ≤ (30161293237007/100000000000000 : ℝ)^3193
        have hw : |(4035091467/10000000000 : ℝ)|=(4035091467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3093/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1899/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8113/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3093/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3093/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3093/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3093/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3093/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3093/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3093/50000 : ℝ) ^ (8433/2048 : ℝ) ≤ (527700960447327/50000000000000000000 : ℝ) := by
    have hpowers : (3093/50000 : ℝ)^8433 ≤ (527700960447327/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3093 : ℕ)^8433*50000000000000000000^2048 ≤ 527700960447327^2048*50000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3093 50000 527700960447327 50000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3093/50000 : ℝ)) (X := (527700960447327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20003/100000 : ℝ) ^ (8433/2048 : ℝ) ≤ (16559467868280947/12500000000000000000 : ℝ) := by
    have hpowers : (20003/100000 : ℝ)^8433 ≤ (16559467868280947/12500000000000000000 : ℝ)^2048 := by
      have hnat : (20003 : ℕ)^8433*12500000000000000000^2048 ≤ 16559467868280947^2048*100000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003 100000 16559467868280947 12500000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20003/100000 : ℝ)) (X := (16559467868280947/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000527700960447327/25000000000000000000 : ℝ) ≤ (5000025630805907/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (25000527700960447327/25000000000000000000 : ℝ)^2048 ≤ (5000025630805907/5000000000000000 : ℝ)^8433 := by
      have hnat : (25000527700960447327 : ℕ)^2048*5000000000000000^8433 ≤ 5000025630805907^8433*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000527700960447327 25000000000000000000 5000025630805907 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000025630805907/5000000000000000 : ℝ)) (X := (25000527700960447327/25000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10013353114486714223/10000000000000000000 : ℝ) ≤ (5001620619290113/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (10013353114486714223/10000000000000000000 : ℝ)^2048 ≤ (5001620619290113/5000000000000000 : ℝ)^8433 := by
      have hnat : (10013353114486714223 : ℕ)^2048*5000000000000000^8433 ≤ 5001620619290113^8433*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013353114486714223 10000000000000000000 5001620619290113 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001620619290113/5000000000000000 : ℝ)) (X := (10013353114486714223/10000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6266559467868280947/6250000000000000000 : ℝ) ≤ (5003215607774319/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (6266559467868280947/6250000000000000000 : ℝ)^2048 ≤ (5003215607774319/5000000000000000 : ℝ)^8433 := by
      have hnat : (6266559467868280947 : ℕ)^2048*5000000000000000^8433 ≤ 5003215607774319^8433*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6266559467868280947 6250000000000000000 5003215607774319 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003215607774319/5000000000000000 : ℝ)) (X := (6266559467868280947/6250000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(527700960447327/50000000000000000000 : ℝ) ≤ ((69065620943318620387/69085000000000000000 : ℝ)+2*(797494242103/345425000000000 : ℝ)*(3093/50000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (69065620943318620387/69085000000000000000 : ℝ)+2*(797494242103/345425000000000 : ℝ)*(3093/50000 : ℝ)=(5000025630805907/5000000000000000 : ℝ) by norm_num, show 1+2*(527700960447327/50000000000000000000 : ℝ)=(25000527700960447327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16559467868280947/12500000000000000000 : ℝ)+(527700960447327/50000000000000000000 : ℝ) ≤ ((69065620943318620387/69085000000000000000 : ℝ)+(797494242103/345425000000000 : ℝ)*((20003/100000 : ℝ)+(3093/50000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (69065620943318620387/69085000000000000000 : ℝ)+(797494242103/345425000000000 : ℝ)*((20003/100000 : ℝ)+(3093/50000 : ℝ))=(5001620619290113/5000000000000000 : ℝ) by norm_num, show 1+(16559467868280947/12500000000000000000 : ℝ)+(527700960447327/50000000000000000000 : ℝ)=(10013353114486714223/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16559467868280947/12500000000000000000 : ℝ) ≤ ((69065620943318620387/69085000000000000000 : ℝ)+2*(797494242103/345425000000000 : ℝ)*(20003/100000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (69065620943318620387/69085000000000000000 : ℝ)+2*(797494242103/345425000000000 : ℝ)*(20003/100000 : ℝ)=(5003215607774319/5000000000000000 : ℝ) by norm_num, show 1+2*(16559467868280947/12500000000000000000 : ℝ)=(6266559467868280947/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69065620943318620387/69085000000000000000 : ℝ)*(X 1 0+X 2 0)+(797494242103/345425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (3093/50000 : ℝ)) (hi := (20003/100000 : ℝ)) (c := (69065620943318620387/69085000000000000000 : ℝ)) (alpha := (797494242103/345425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69065620943318620387/69085000000000000000 : ℝ)*(X 0 1+X 2 1)+(797494242103/345425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (3093/50000 : ℝ)) (hi := (20003/100000 : ℝ)) (c := (69065620943318620387/69085000000000000000 : ℝ)) (alpha := (797494242103/345425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69065620943318620387/69085000000000000000 : ℝ)*(X 0 2+X 1 2)+(797494242103/345425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (3093/50000 : ℝ)) (hi := (20003/100000 : ℝ)) (c := (69065620943318620387/69085000000000000000 : ℝ)) (alpha := (797494242103/345425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421289047/2000000000 : ℝ)*X 0 0+(686619959/1250000000 : ℝ)*X 0 1+(5174553231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342431717/2500000000 : ℝ)*X 1 0+(-1135691611/5000000000 : ℝ)*X 1 1+(5174553233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073945343/2000000000 : ℝ)*X 2 0+(1293638339/2500000000 : ℝ)*X 2 1+(-2271383263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171080137/5000000000 : ℝ)*X 0 0+(4030898727/10000000000 : ℝ)*X 0 1+(935336787/2000000000 : ℝ)*X 0 2+(2171080137/5000000000 : ℝ)*X 1 0+(4030898727/10000000000 : ℝ)*X 1 1+(935336787/2000000000 : ℝ)*X 1 2+(2171080137/5000000000 : ℝ)*X 2 0+(4030898727/10000000000 : ℝ)*X 2 1+(935336787/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1053261931/5000000000 : ℝ)*X 0 0+(2588300767/5000000000 : ℝ)*X 0 1+(5490892149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644209691/5000000000 : ℝ)*X 1 0+(-244380511/1250000000 : ℝ)*X 1 1+(5490892193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288419549/10000000000 : ℝ)*X 2 0+(5490892273/10000000000 : ℝ)*X 2 1+(-488760937/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342319209/10000000000 : ℝ)*X 0 0+(4672529863/10000000000 : ℝ)*X 0 1+(4035091467/10000000000 : ℝ)*X 0 2+(4342319209/10000000000 : ℝ)*X 1 0+(4672529863/10000000000 : ℝ)*X 1 1+(4035091467/10000000000 : ℝ)*X 1 2+(4342319209/10000000000 : ℝ)*X 2 0+(4672529863/10000000000 : ℝ)*X 2 1+(4035091467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7446713006330062220198837277/863562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104672359/6250000000000 : ℝ)*(base19) + (736059827/50000000000000 : ℝ)*(base23) + (237339/390625000000 : ℝ)*(lower2) + (260930773/100000000000000 : ℝ)*(upper3) + (118054501/100000000000000 : ℝ)*(upper5) + (586149774352343/25000000000000 : ℝ)*(major0) + (586149774352343/25000000000000 : ℝ)*(major1) + (586149774352343/25000000000000 : ℝ)*(major2) + (98145615893167/3125000000000 : ℝ)*(sp0) + (3140675352046747/100000000000000 : ℝ)*(sp1) + (1570337777342419/50000000000000 : ℝ)*(sp2) + (154851096906607/10000000000000 : ℝ)*(sp3) + (4329555787/25000000000000 : ℝ)*(sp4) + (49557533/500000000000 : ℝ)*(sp7) + (154852088057267/10000000000000 : ℝ)*(f.failure) + (3140677026804491/100000000000000 : ℝ)*(f.sum) + (51645903365581/17271250000000000000000000000 : ℝ)*base65 + (488550483525566741/1727125000000000000000000000000000 : ℝ)*base67 + (14403754563910933259/1727125000000000000000000000000000 : ℝ)*base70 + (7095107433992816741/1727125000000000000000000000000000 : ℝ)*base71 + (24552813490969/4317812500000000000000000000 : ℝ)*base73 + (6578749347702191741/1727125000000000000000000000000000 : ℝ)*base75 + (3889306482698066741/1727125000000000000000000000000000 : ℝ)*base77 + (18476228702046433259/1727125000000000000000000000000000 : ℝ)*base80 + (9233990564187/8635625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (61219/1000000000000000000000 : ℝ)*base90 + (61219/1000000000000000000000 : ℝ)*base92 + (61219/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (582958412635782485374779/69085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416734323/20000000000000 : ℝ)*(base19) + (2320107717/100000000000000 : ℝ)*(base23) + (24426659/100000000000000 : ℝ)*(upper2) + (17277681/6250000000000 : ℝ)*(upper3) + (33327093/20000000000000 : ℝ)*(upper5) + (1187636831393383/50000000000000 : ℝ)*(major0) + (1187636831393383/50000000000000 : ℝ)*(major1) + (1187636831393383/50000000000000 : ℝ)*(major2) + (856178919/4000000000000 : ℝ)*(sp1) + (1702721921/6250000000000 : ℝ)*(sp2) + (1590883374604227/50000000000000 : ℝ)*(sp4) + (397717907632983/12500000000000 : ℝ)*(sp5) + (63634743711/2000000000 : ℝ)*(sp6) + (1532012006923/97656250000 : ℝ)*(sp7) + (1532012006923/97656250000 : ℝ)*(f.failure) + (1590883374604227/50000000000000 : ℝ)*(f.sum) + (38775619096223/17271250000000000000000000000 : ℝ)*base65 + (6148582200170500779/3454250000000000000000000000000000 : ℝ)*base68 + (7081157223097000779/3454250000000000000000000000000000 : ℝ)*base70 + (6670448691387499221/3454250000000000000000000000000000 : ℝ)*base71 + (51219722775301/34542500000000000000000000000 : ℝ)*base73 + (17880401040741250779/3454250000000000000000000000000000 : ℝ)*base76 + (22838902117946499221/3454250000000000000000000000000000 : ℝ)*base77 + (6569788129614499221/3454250000000000000000000000000000 : ℝ)*base79 + (17074761186721/8635625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9597/19531250000000000000 : ℝ)*base90 + (9597/19531250000000000000 : ℝ)*base92 + (9597/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1241_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3093/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1241_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1241_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1241_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1241_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
