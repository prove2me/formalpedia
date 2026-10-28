-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1194_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:21.99+00:00
-- url     : https://prove2.me/submissions/0a63ad05-7910-43b6-923c-a30f6540181e

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
theorem support_rectangle_w1194_s3_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267374523/1250000000 : ℝ)*x 0 + (216961171/400000000 : ℝ)*x 1 + (1047347821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267374523/1250000000 : ℝ)^8387 ≤ (2599229879079/20000000000000 : ℝ)^6339 := by
    have hnat : (267374523 : ℕ)^8387*20000000000000^6339 ≤ 2599229879079^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267374523 1250000000 2599229879079 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216961171/400000000 : ℝ)^8387 ≤ (8902601893047/20000000000000 : ℝ)^6339 := by
    have hnat : (216961171 : ℕ)^8387*20000000000000^6339 ≤ 8902601893047^6339*400000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216961171 400000000 8902601893047 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047347821/2000000000 : ℝ)^8387 ≤ (42490841124933/100000000000000 : ℝ)^6339 := by
    have hnat : (1047347821 : ℕ)^8387*100000000000000^6339 ≤ 42490841124933^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047347821 2000000000 42490841124933 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267374523/1250000000 : ℝ), (216961171/400000000 : ℝ), (1047347821/2000000000 : ℝ)] ![(2599229879079/20000000000000 : ℝ), (8902601893047/20000000000000 : ℝ), (42490841124933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267374523/1250000000 : ℝ)|^8387 ≤ (2599229879079/20000000000000 : ℝ)^6339
        have hw : |(-267374523/1250000000 : ℝ)|=(267374523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216961171/400000000 : ℝ)|^8387 ≤ (8902601893047/20000000000000 : ℝ)^6339
        have hw : |(216961171/400000000 : ℝ)|=(216961171/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047347821/2000000000 : ℝ)|^8387 ≤ (42490841124933/100000000000000 : ℝ)^6339
        have hw : |(1047347821/2000000000 : ℝ)|=(1047347821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s3_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352568833/10000000000 : ℝ)*x 0 + (-279328487/1250000000 : ℝ)*x 1 + (5236739357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352568833/10000000000 : ℝ)^8387 ≤ (21869373255543/50000000000000 : ℝ)^6339 := by
    have hnat : (5352568833 : ℕ)^8387*50000000000000^6339 ≤ 21869373255543^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352568833 10000000000 21869373255543 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279328487/1250000000 : ℝ)^8387 ≤ (13770409651743/100000000000000 : ℝ)^6339 := by
    have hnat : (279328487 : ℕ)^8387*100000000000000^6339 ≤ 13770409651743^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279328487 1250000000 13770409651743 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236739357/10000000000 : ℝ)^8387 ≤ (42490843830267/100000000000000 : ℝ)^6339 := by
    have hnat : (5236739357 : ℕ)^8387*100000000000000^6339 ≤ 42490843830267^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236739357 10000000000 42490843830267 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352568833/10000000000 : ℝ), (-279328487/1250000000 : ℝ), (5236739357/10000000000 : ℝ)] ![(21869373255543/50000000000000 : ℝ), (13770409651743/100000000000000 : ℝ), (42490843830267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352568833/10000000000 : ℝ)|^8387 ≤ (21869373255543/50000000000000 : ℝ)^6339
        have hw : |(5352568833/10000000000 : ℝ)|=(5352568833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279328487/1250000000 : ℝ)|^8387 ≤ (13770409651743/100000000000000 : ℝ)^6339
        have hw : |(-279328487/1250000000 : ℝ)|=(279328487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236739357/10000000000 : ℝ)|^8387 ≤ (42490843830267/100000000000000 : ℝ)^6339
        have hw : |(5236739357/10000000000 : ℝ)|=(5236739357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s3_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352568693/10000000000 : ℝ)*x 0 + (5236739621/10000000000 : ℝ)*x 1 + (-2234627733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352568693/10000000000 : ℝ)^8387 ≤ (43738744997463/100000000000000 : ℝ)^6339 := by
    have hnat : (5352568693 : ℕ)^8387*100000000000000^6339 ≤ 43738744997463^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352568693 10000000000 43738744997463 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236739621/10000000000 : ℝ)^8387 ≤ (21245423332213/50000000000000 : ℝ)^6339 := by
    have hnat : (5236739621 : ℕ)^8387*50000000000000^6339 ≤ 21245423332213^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236739621 10000000000 21245423332213 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234627733/10000000000 : ℝ)^8387 ≤ (13770408322773/100000000000000 : ℝ)^6339 := by
    have hnat : (2234627733 : ℕ)^8387*100000000000000^6339 ≤ 13770408322773^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234627733 10000000000 13770408322773 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352568693/10000000000 : ℝ), (5236739621/10000000000 : ℝ), (-2234627733/10000000000 : ℝ)] ![(43738744997463/100000000000000 : ℝ), (21245423332213/50000000000000 : ℝ), (13770408322773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352568693/10000000000 : ℝ)|^8387 ≤ (43738744997463/100000000000000 : ℝ)^6339
        have hw : |(5352568693/10000000000 : ℝ)|=(5352568693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236739621/10000000000 : ℝ)|^8387 ≤ (21245423332213/50000000000000 : ℝ)^6339
        have hw : |(5236739621/10000000000 : ℝ)|=(5236739621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234627733/10000000000 : ℝ)|^8387 ≤ (13770408322773/100000000000000 : ℝ)^6339
        have hw : |(-2234627733/10000000000 : ℝ)|=(2234627733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s3_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87109029/200000000 : ℝ)*x 0 + (166849531/400000000 : ℝ)*x 1 + (2273825369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87109029/200000000 : ℝ)^8387 ≤ (33297547757951/100000000000000 : ℝ)^6339 := by
    have hnat : (87109029 : ℕ)^8387*100000000000000^6339 ≤ 33297547757951^6339*200000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87109029 200000000 33297547757951 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166849531/400000000 : ℝ)^8387 ≤ (3930886231453/12500000000000 : ℝ)^6339 := by
    have hnat : (166849531 : ℕ)^8387*12500000000000^6339 ≤ 3930886231453^6339*400000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166849531 400000000 3930886231453 12500000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273825369/5000000000 : ℝ)^8387 ≤ (35255362376633/100000000000000 : ℝ)^6339 := by
    have hnat : (2273825369 : ℕ)^8387*100000000000000^6339 ≤ 35255362376633^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273825369 5000000000 35255362376633 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87109029/200000000 : ℝ), (166849531/400000000 : ℝ), (2273825369/5000000000 : ℝ)] ![(33297547757951/100000000000000 : ℝ), (3930886231453/12500000000000 : ℝ), (35255362376633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87109029/200000000 : ℝ)|^8387 ≤ (33297547757951/100000000000000 : ℝ)^6339
        have hw : |(87109029/200000000 : ℝ)|=(87109029/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166849531/400000000 : ℝ)|^8387 ≤ (3930886231453/12500000000000 : ℝ)^6339
        have hw : |(166849531/400000000 : ℝ)|=(166849531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273825369/5000000000 : ℝ)|^8387 ≤ (35255362376633/100000000000000 : ℝ)^6339
        have hw : |(2273825369/5000000000 : ℝ)|=(2273825369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s3_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139012119/10000000000 : ℝ)*x 0 + (5237440971/10000000000 : ℝ)*x 1 + (1084664701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139012119/10000000000 : ℝ)^8387 ≤ (3249069373409/25000000000000 : ℝ)^6339 := by
    have hnat : (2139012119 : ℕ)^8387*25000000000000^6339 ≤ 3249069373409^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139012119 10000000000 3249069373409 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237440971/10000000000 : ℝ)^8387 ≤ (424983761359/1000000000000 : ℝ)^6339 := by
    have hnat : (5237440971 : ℕ)^8387*1000000000000^6339 ≤ 424983761359^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237440971 10000000000 424983761359 1000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084664701/2000000000 : ℝ)^8387 ≤ (11126336589563/25000000000000 : ℝ)^6339 := by
    have hnat : (1084664701 : ℕ)^8387*25000000000000^6339 ≤ 11126336589563^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084664701 2000000000 11126336589563 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139012119/10000000000 : ℝ), (5237440971/10000000000 : ℝ), (1084664701/2000000000 : ℝ)] ![(3249069373409/25000000000000 : ℝ), (424983761359/1000000000000 : ℝ), (11126336589563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139012119/10000000000 : ℝ)|^8387 ≤ (3249069373409/25000000000000 : ℝ)^6339
        have hw : |(-2139012119/10000000000 : ℝ)|=(2139012119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237440971/10000000000 : ℝ)|^8387 ≤ (424983761359/1000000000000 : ℝ)^6339
        have hw : |(5237440971/10000000000 : ℝ)|=(5237440971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084664701/2000000000 : ℝ)|^8387 ≤ (11126336589563/25000000000000 : ℝ)^6339
        have hw : |(1084664701/2000000000 : ℝ)|=(1084664701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s3_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304943717/10000000000 : ℝ)*x 0 + (-1024021671/5000000000 : ℝ)*x 1 + (5423323433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304943717/10000000000 : ℝ)^8387 ≤ (21612292193407/50000000000000 : ℝ)^6339 := by
    have hnat : (5304943717 : ℕ)^8387*50000000000000^6339 ≤ 21612292193407^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304943717 10000000000 21612292193407 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024021671/5000000000 : ℝ)^8387 ≤ (3067517505953/25000000000000 : ℝ)^6339 := by
    have hnat : (1024021671 : ℕ)^8387*25000000000000^6339 ≤ 3067517505953^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024021671 5000000000 3067517505953 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423323433/10000000000 : ℝ)^8387 ≤ (44505345576507/100000000000000 : ℝ)^6339 := by
    have hnat : (5423323433 : ℕ)^8387*100000000000000^6339 ≤ 44505345576507^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423323433 10000000000 44505345576507 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304943717/10000000000 : ℝ), (-1024021671/5000000000 : ℝ), (5423323433/10000000000 : ℝ)] ![(21612292193407/50000000000000 : ℝ), (3067517505953/25000000000000 : ℝ), (44505345576507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304943717/10000000000 : ℝ)|^8387 ≤ (21612292193407/50000000000000 : ℝ)^6339
        have hw : |(5304943717/10000000000 : ℝ)|=(5304943717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024021671/5000000000 : ℝ)|^8387 ≤ (3067517505953/25000000000000 : ℝ)^6339
        have hw : |(-1024021671/5000000000 : ℝ)|=(1024021671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423323433/10000000000 : ℝ)|^8387 ≤ (44505345576507/100000000000000 : ℝ)^6339
        have hw : |(5423323433/10000000000 : ℝ)|=(5423323433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s3_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304943339/10000000000 : ℝ)*x 0 + (5423323841/10000000000 : ℝ)*x 1 + (-2048043297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304943339/10000000000 : ℝ)^8387 ≤ (43224580311813/100000000000000 : ℝ)^6339 := by
    have hnat : (5304943339 : ℕ)^8387*100000000000000^6339 ≤ 43224580311813^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304943339 10000000000 43224580311813 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423323841/10000000000 : ℝ)^8387 ≤ (8901070001279/20000000000000 : ℝ)^6339 := by
    have hnat : (5423323841 : ℕ)^8387*20000000000000^6339 ≤ 8901070001279^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423323841 10000000000 8901070001279 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048043297/10000000000 : ℝ)^8387 ≤ (1227006966711/10000000000000 : ℝ)^6339 := by
    have hnat : (2048043297 : ℕ)^8387*10000000000000^6339 ≤ 1227006966711^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048043297 10000000000 1227006966711 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304943339/10000000000 : ℝ), (5423323841/10000000000 : ℝ), (-2048043297/10000000000 : ℝ)] ![(43224580311813/100000000000000 : ℝ), (8901070001279/20000000000000 : ℝ), (1227006966711/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304943339/10000000000 : ℝ)|^8387 ≤ (43224580311813/100000000000000 : ℝ)^6339
        have hw : |(5304943339/10000000000 : ℝ)|=(5304943339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423323841/10000000000 : ℝ)|^8387 ≤ (8901070001279/20000000000000 : ℝ)^6339
        have hw : |(5423323841/10000000000 : ℝ)|=(5423323841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048043297/10000000000 : ℝ)|^8387 ≤ (1227006966711/10000000000000 : ℝ)^6339
        have hw : |(-2048043297/10000000000 : ℝ)|=(2048043297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s3_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355483659/10000000000 : ℝ)*x 0 + (4546239851/10000000000 : ℝ)*x 1 + (2086328143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355483659/10000000000 : ℝ)^8387 ≤ (33297873551683/100000000000000 : ℝ)^6339 := by
    have hnat : (4355483659 : ℕ)^8387*100000000000000^6339 ≤ 33297873551683^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355483659 10000000000 33297873551683 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4546239851/10000000000 : ℝ)^8387 ≤ (35240891513521/100000000000000 : ℝ)^6339 := by
    have hnat : (4546239851 : ℕ)^8387*100000000000000^6339 ≤ 35240891513521^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546239851 10000000000 35240891513521 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086328143/5000000000 : ℝ)^8387 ≤ (15730617455921/50000000000000 : ℝ)^6339 := by
    have hnat : (2086328143 : ℕ)^8387*50000000000000^6339 ≤ 15730617455921^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086328143 5000000000 15730617455921 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355483659/10000000000 : ℝ), (4546239851/10000000000 : ℝ), (2086328143/5000000000 : ℝ)] ![(33297873551683/100000000000000 : ℝ), (35240891513521/100000000000000 : ℝ), (15730617455921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355483659/10000000000 : ℝ)|^8387 ≤ (33297873551683/100000000000000 : ℝ)^6339
        have hw : |(4355483659/10000000000 : ℝ)|=(4355483659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4546239851/10000000000 : ℝ)|^8387 ≤ (35240891513521/100000000000000 : ℝ)^6339
        have hw : |(4546239851/10000000000 : ℝ)|=(4546239851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086328143/5000000000 : ℝ)|^8387 ≤ (15730617455921/50000000000000 : ℝ)^6339
        have hw : |(2086328143/5000000000 : ℝ)|=(2086328143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (337/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9299/100000 : ℝ) ^ (4193/1024 : ℝ) ≤ (2985372355419717/50000000000000000000 : ℝ) := by
    have hpowers : (9299/100000 : ℝ)^4193 ≤ (2985372355419717/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9299 : ℕ)^4193*50000000000000000000^1024 ≤ 2985372355419717^1024*100000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9299 100000 2985372355419717 50000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9299/100000 : ℝ)) (X := (2985372355419717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (511/3125 : ℝ) ^ (4193/1024 : ℝ) ≤ (30113261173862491/50000000000000000000 : ℝ) := by
    have hpowers : (511/3125 : ℝ)^4193 ≤ (30113261173862491/50000000000000000000 : ℝ)^1024 := by
      have hnat : (511 : ℕ)^4193*50000000000000000000^1024 ≤ 30113261173862491^1024*3125^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        511 3125 30113261173862491 50000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (511/3125 : ℝ)) (X := (30113261173862491/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002985372355419717/25000000000000000000 : ℝ) ≤ (250007290444433/250000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (25002985372355419717/25000000000000000000 : ℝ)^1024 ≤ (250007290444433/250000000000000 : ℝ)^4193 := by
      have hnat : (25002985372355419717 : ℕ)^1024*250000000000000^4193 ≤ 250007290444433^4193*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002985372355419717 25000000000000000000 250007290444433 250000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250007290444433/250000000000000 : ℝ)) (X := (25002985372355419717/25000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563534332297790069/1562500000000000000 : ℝ) ≤ (10001616242573231/10000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (1563534332297790069/1562500000000000000 : ℝ)^1024 ≤ (10001616242573231/10000000000000000 : ℝ)^4193 := by
      have hnat : (1563534332297790069 : ℕ)^1024*10000000000000000^4193 ≤ 10001616242573231^4193*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563534332297790069 1562500000000000000 10001616242573231 10000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001616242573231/10000000000000000 : ℝ)) (X := (1563534332297790069/1562500000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030113261173862491/25000000000000000000 : ℝ) ≤ (5001470433684571/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (25030113261173862491/25000000000000000000 : ℝ)^1024 ≤ (5001470433684571/5000000000000000 : ℝ)^4193 := by
      have hnat : (25030113261173862491 : ℕ)^1024*5000000000000000^4193 ≤ 5001470433684571^4193*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030113261173862491 25000000000000000000 5001470433684571 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001470433684571/5000000000000000 : ℝ)) (X := (25030113261173862491/25000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2985372355419717/50000000000000000000 : ℝ) ≤ ((11751236901371514197/11755000000000000000 : ℝ)+2*(441541598637/235100000000000 : ℝ)*(9299/100000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (11751236901371514197/11755000000000000000 : ℝ)+2*(441541598637/235100000000000 : ℝ)*(9299/100000 : ℝ)=(250007290444433/250000000000000 : ℝ) by norm_num, show 1+2*(2985372355419717/50000000000000000000 : ℝ)=(25002985372355419717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30113261173862491/50000000000000000000 : ℝ)+(2985372355419717/50000000000000000000 : ℝ) ≤ ((11751236901371514197/11755000000000000000 : ℝ)+(441541598637/235100000000000 : ℝ)*((511/3125 : ℝ)+(9299/100000 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (11751236901371514197/11755000000000000000 : ℝ)+(441541598637/235100000000000 : ℝ)*((511/3125 : ℝ)+(9299/100000 : ℝ))=(10001616242573231/10000000000000000 : ℝ) by norm_num, show 1+(30113261173862491/50000000000000000000 : ℝ)+(2985372355419717/50000000000000000000 : ℝ)=(1563534332297790069/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30113261173862491/50000000000000000000 : ℝ) ≤ ((11751236901371514197/11755000000000000000 : ℝ)+2*(441541598637/235100000000000 : ℝ)*(511/3125 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (11751236901371514197/11755000000000000000 : ℝ)+2*(441541598637/235100000000000 : ℝ)*(511/3125 : ℝ)=(5001470433684571/5000000000000000 : ℝ) by norm_num, show 1+2*(30113261173862491/50000000000000000000 : ℝ)=(25030113261173862491/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11751236901371514197/11755000000000000000 : ℝ)*(X 1 0+X 2 0)+(441541598637/235100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (9299/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (11751236901371514197/11755000000000000000 : ℝ)) (alpha := (441541598637/235100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11751236901371514197/11755000000000000000 : ℝ)*(X 0 1+X 2 1)+(441541598637/235100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (9299/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (11751236901371514197/11755000000000000000 : ℝ)) (alpha := (441541598637/235100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11751236901371514197/11755000000000000000 : ℝ)*(X 0 2+X 1 2)+(441541598637/235100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (9299/100000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (11751236901371514197/11755000000000000000 : ℝ)) (alpha := (441541598637/235100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267374523/1250000000 : ℝ)*X 0 0+(216961171/400000000 : ℝ)*X 0 1+(1047347821/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352568833/10000000000 : ℝ)*X 1 0+(-279328487/1250000000 : ℝ)*X 1 1+(5236739357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352568693/10000000000 : ℝ)*X 2 0+(5236739621/10000000000 : ℝ)*X 2 1+(-2234627733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87109029/200000000 : ℝ)*X 0 0+(166849531/400000000 : ℝ)*X 0 1+(2273825369/5000000000 : ℝ)*X 0 2+(87109029/200000000 : ℝ)*X 1 0+(166849531/400000000 : ℝ)*X 1 1+(2273825369/5000000000 : ℝ)*X 1 2+(87109029/200000000 : ℝ)*X 2 0+(166849531/400000000 : ℝ)*X 2 1+(2273825369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139012119/10000000000 : ℝ)*X 0 0+(5237440971/10000000000 : ℝ)*X 0 1+(1084664701/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304943717/10000000000 : ℝ)*X 1 0+(-1024021671/5000000000 : ℝ)*X 1 1+(5423323433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304943339/10000000000 : ℝ)*X 2 0+(5423323841/10000000000 : ℝ)*X 2 1+(-2048043297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355483659/10000000000 : ℝ)*X 0 0+(4546239851/10000000000 : ℝ)*X 0 1+(2086328143/5000000000 : ℝ)*X 0 2+(4355483659/10000000000 : ℝ)*X 1 0+(4546239851/10000000000 : ℝ)*X 1 1+(2086328143/5000000000 : ℝ)*X 1 2+(4355483659/10000000000 : ℝ)*X 2 0+(4546239851/10000000000 : ℝ)*X 2 1+(2086328143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (739114454683668828776729529/146937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130262053/25000000000000 : ℝ)*(base19) + (252944587/100000000000000 : ℝ)*(base23) + (13750697/20000000000000 : ℝ)*(lower2) + (9660443/50000000000000 : ℝ)*(upper3) + (18807687/25000000000000 : ℝ)*(upper5) + (1999004693585819/50000000000000 : ℝ)*(major0) + (1999004693585819/50000000000000 : ℝ)*(major1) + (1999004693585819/50000000000000 : ℝ)*(major2) + (266966278573217/5000000000000 : ℝ)*(sp0) + (266967226394967/5000000000000 : ℝ)*(sp1) + (1334836199000741/25000000000000 : ℝ)*(sp2) + (83020850788147/3125000000000 : ℝ)*(sp3) + (19477483211/100000000000000 : ℝ)*(sp4) + (6332504071/100000000000000 : ℝ)*(sp7) + (106266942308991/4000000000000 : ℝ)*(f.failure) + (5339345048947551/100000000000000 : ℝ)*(f.sum) + (42246636938903/5877500000000000000000000000 : ℝ)*base65 + (7752736046743977657/587750000000000000000000000000000 : ℝ)*base68 + (4497623561884227657/587750000000000000000000000000000 : ℝ)*base70 + (2373352059958227657/587750000000000000000000000000000 : ℝ)*base72 + (27238077071249/11755000000000000000000000000 : ℝ)*base74 + (16524242893852977657/587750000000000000000000000000000 : ℝ)*base76 + (9148701554783772343/587750000000000000000000000000000 : ℝ)*base77 + (12441597050072227657/587750000000000000000000000000000 : ℝ)*base80 + (4545003344831/2938750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1339159/200000000000000000000 : ℝ)*base89 + (1339159/200000000000000000000 : ℝ)*base91 + (1339159/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (492184921294517878813077327/587750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233150467/25000000000000 : ℝ)*(base19) + (355083969/50000000000000 : ℝ)*(base23) + (6621953/100000000000000 : ℝ)*(upper3) + (22030057/25000000000000 : ℝ)*(lower4) + (13792001/10000000000000 : ℝ)*(upper5) + (4028257629506097/100000000000000 : ℝ)*(major0) + (4028257629506097/100000000000000 : ℝ)*(major1) + (4028257629506097/100000000000000 : ℝ)*(major2) + (20444703969/100000000000000 : ℝ)*(sp1) + (9931913151/50000000000000 : ℝ)*(sp2) + (2689870872092641/50000000000000 : ℝ)*(sp4) + (1075944073375889/20000000000000 : ℝ)*(sp5) + (2689860585095521/50000000000000 : ℝ)*(sp6) + (13383867434567/500000000000 : ℝ)*(sp7) + (13383867434567/500000000000 : ℝ)*(f.failure) + (2689870872092641/50000000000000 : ℝ)*(f.sum) + (15517427093921/11755000000000000000000000000 : ℝ)*base66 + (3768508109337990891/1175500000000000000000000000000000 : ℝ)*base68 + (1859723672031990891/1175500000000000000000000000000000 : ℝ)*base70 + (8461589470352009109/1175500000000000000000000000000000 : ℝ)*base71 + (929248090641/11755000000000000000000000000 : ℝ)*base74 + (20609618863964009109/1175500000000000000000000000000000 : ℝ)*base75 + (3129472104638990891/1175500000000000000000000000000000 : ℝ)*base78 + (3752703561208990891/1175500000000000000000000000000000 : ℝ)*base80 + (32648641208011/11755000000000000000000000000 : ℝ)*base82 + (131983/25000000000000000000 : ℝ)*base89 + (131983/25000000000000000000 : ℝ)*base91 + (131983/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1194_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (337/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1194_s4_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070802471/5000000000 : ℝ)*x 0 + (5399504273/10000000000 : ℝ)*x 1 + (5259556103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070802471/5000000000 : ℝ)^8387 ≤ (6508562389249/50000000000000 : ℝ)^6339 := by
    have hnat : (1070802471 : ℕ)^8387*50000000000000^6339 ≤ 6508562389249^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070802471 5000000000 6508562389249 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399504273/10000000000 : ℝ)^8387 ≤ (22123455545213/50000000000000 : ℝ)^6339 := by
    have hnat : (5399504273 : ℕ)^8387*50000000000000^6339 ≤ 22123455545213^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399504273 10000000000 22123455545213 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259556103/10000000000 : ℝ)^8387 ≤ (21367982060009/50000000000000 : ℝ)^6339 := by
    have hnat : (5259556103 : ℕ)^8387*50000000000000^6339 ≤ 21367982060009^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259556103 10000000000 21367982060009 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070802471/5000000000 : ℝ), (5399504273/10000000000 : ℝ), (5259556103/10000000000 : ℝ)] ![(6508562389249/50000000000000 : ℝ), (22123455545213/50000000000000 : ℝ), (21367982060009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070802471/5000000000 : ℝ)|^8387 ≤ (6508562389249/50000000000000 : ℝ)^6339
        have hw : |(-1070802471/5000000000 : ℝ)|=(1070802471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399504273/10000000000 : ℝ)|^8387 ≤ (22123455545213/50000000000000 : ℝ)^6339
        have hw : |(5399504273/10000000000 : ℝ)|=(5399504273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259556103/10000000000 : ℝ)|^8387 ≤ (21367982060009/50000000000000 : ℝ)^6339
        have hw : |(5259556103/10000000000 : ℝ)|=(5259556103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s4_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673207039/5000000000 : ℝ)*x 0 + (-1106344311/5000000000 : ℝ)*x 1 + (5259556179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673207039/5000000000 : ℝ)^8387 ≤ (43672216126443/100000000000000 : ℝ)^6339 := by
    have hnat : (2673207039 : ℕ)^8387*100000000000000^6339 ≤ 43672216126443^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673207039 5000000000 43672216126443 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106344311/5000000000 : ℝ)^8387 ≤ (13591818916151/100000000000000 : ℝ)^6339 := by
    have hnat : (1106344311 : ℕ)^8387*100000000000000^6339 ≤ 13591818916151^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106344311 5000000000 13591818916151 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259556179/10000000000 : ℝ)^8387 ≤ (2136798246853/5000000000000 : ℝ)^6339 := by
    have hnat : (5259556179 : ℕ)^8387*5000000000000^6339 ≤ 2136798246853^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259556179 10000000000 2136798246853 5000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673207039/5000000000 : ℝ), (-1106344311/5000000000 : ℝ), (5259556179/10000000000 : ℝ)] ![(43672216126443/100000000000000 : ℝ), (13591818916151/100000000000000 : ℝ), (2136798246853/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673207039/5000000000 : ℝ)|^8387 ≤ (43672216126443/100000000000000 : ℝ)^6339
        have hw : |(2673207039/5000000000 : ℝ)|=(2673207039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106344311/5000000000 : ℝ)|^8387 ≤ (13591818916151/100000000000000 : ℝ)^6339
        have hw : |(-1106344311/5000000000 : ℝ)|=(1106344311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259556179/10000000000 : ℝ)|^8387 ≤ (2136798246853/5000000000000 : ℝ)^6339
        have hw : |(5259556179/10000000000 : ℝ)|=(5259556179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s4_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346413969/10000000000 : ℝ)*x 0 + (5259556073/10000000000 : ℝ)*x 1 + (-553172227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346413969/10000000000 : ℝ)^8387 ≤ (682378358569/1562500000000 : ℝ)^6339 := by
    have hnat : (5346413969 : ℕ)^8387*1562500000000^6339 ≤ 682378358569^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346413969 10000000000 682378358569 1562500000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259556073/10000000000 : ℝ)^8387 ≤ (21367981898751/50000000000000 : ℝ)^6339 := by
    have hnat : (5259556073 : ℕ)^8387*50000000000000^6339 ≤ 21367981898751^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259556073 10000000000 21367981898751 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553172227/2500000000 : ℝ)^8387 ≤ (13591821240543/100000000000000 : ℝ)^6339 := by
    have hnat : (553172227 : ℕ)^8387*100000000000000^6339 ≤ 13591821240543^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553172227 2500000000 13591821240543 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346413969/10000000000 : ℝ), (5259556073/10000000000 : ℝ), (-553172227/2500000000 : ℝ)] ![(682378358569/1562500000000 : ℝ), (21367981898751/50000000000000 : ℝ), (13591821240543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346413969/10000000000 : ℝ)|^8387 ≤ (682378358569/1562500000000 : ℝ)^6339
        have hw : |(5346413969/10000000000 : ℝ)|=(5346413969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259556073/10000000000 : ℝ)|^8387 ≤ (21367981898751/50000000000000 : ℝ)^6339
        have hw : |(5259556073/10000000000 : ℝ)|=(5259556073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553172227/2500000000 : ℝ)|^8387 ≤ (13591821240543/100000000000000 : ℝ)^6339
        have hw : |(-553172227/2500000000 : ℝ)|=(553172227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s4_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357013073/10000000000 : ℝ)*x 0 + (4218610507/10000000000 : ℝ)*x 1 + (4499876897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357013073/10000000000 : ℝ)^8387 ≤ (33313344455851/100000000000000 : ℝ)^6339 := by
    have hnat : (4357013073 : ℕ)^8387*100000000000000^6339 ≤ 33313344455851^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357013073 10000000000 33313344455851 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218610507/10000000000 : ℝ)^8387 ≤ (6384095995197/20000000000000 : ℝ)^6339 := by
    have hnat : (4218610507 : ℕ)^8387*20000000000000^6339 ≤ 6384095995197^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218610507 10000000000 6384095995197 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499876897/10000000000 : ℝ)^8387 ≤ (34766175555361/100000000000000 : ℝ)^6339 := by
    have hnat : (4499876897 : ℕ)^8387*100000000000000^6339 ≤ 34766175555361^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499876897 10000000000 34766175555361 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357013073/10000000000 : ℝ), (4218610507/10000000000 : ℝ), (4499876897/10000000000 : ℝ)] ![(33313344455851/100000000000000 : ℝ), (6384095995197/20000000000000 : ℝ), (34766175555361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357013073/10000000000 : ℝ)|^8387 ≤ (33313344455851/100000000000000 : ℝ)^6339
        have hw : |(4357013073/10000000000 : ℝ)|=(4357013073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4218610507/10000000000 : ℝ)|^8387 ≤ (6384095995197/20000000000000 : ℝ)^6339
        have hw : |(4218610507/10000000000 : ℝ)|=(4218610507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499876897/10000000000 : ℝ)|^8387 ≤ (34766175555361/100000000000000 : ℝ)^6339
        have hw : |(4499876897/10000000000 : ℝ)|=(4499876897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s4_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-214161163/1000000000 : ℝ)*x 0 + (5259948677/10000000000 : ℝ)*x 1 + (1079822009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214161163/1000000000 : ℝ)^8387 ≤ (2603435712623/20000000000000 : ℝ)^6339 := by
    have hnat : (214161163 : ℕ)^8387*20000000000000^6339 ≤ 2603435712623^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214161163 1000000000 2603435712623 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259948677/10000000000 : ℝ)^8387 ≤ (8548036910729/20000000000000 : ℝ)^6339 := by
    have hnat : (5259948677 : ℕ)^8387*20000000000000^6339 ≤ 8548036910729^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259948677 10000000000 8548036910729 20000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079822009/2000000000 : ℝ)^8387 ≤ (22121318433087/50000000000000 : ℝ)^6339 := by
    have hnat : (1079822009 : ℕ)^8387*50000000000000^6339 ≤ 22121318433087^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079822009 2000000000 22121318433087 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214161163/1000000000 : ℝ), (5259948677/10000000000 : ℝ), (1079822009/2000000000 : ℝ)] ![(2603435712623/20000000000000 : ℝ), (8548036910729/20000000000000 : ℝ), (22121318433087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214161163/1000000000 : ℝ)|^8387 ≤ (2603435712623/20000000000000 : ℝ)^6339
        have hw : |(-214161163/1000000000 : ℝ)|=(214161163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259948677/10000000000 : ℝ)|^8387 ≤ (8548036910729/20000000000000 : ℝ)^6339
        have hw : |(5259948677/10000000000 : ℝ)|=(5259948677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079822009/2000000000 : ℝ)|^8387 ≤ (22121318433087/50000000000000 : ℝ)^6339
        have hw : |(1079822009/2000000000 : ℝ)|=(1079822009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s4_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655412939/5000000000 : ℝ)*x 0 + (-259141873/1250000000 : ℝ)*x 1 + (2699554933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655412939/5000000000 : ℝ)^8387 ≤ (43288007945561/100000000000000 : ℝ)^6339 := by
    have hnat : (2655412939 : ℕ)^8387*100000000000000^6339 ≤ 43288007945561^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655412939 5000000000 43288007945561 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259141873/1250000000 : ℝ)^8387 ≤ (6234678559757/50000000000000 : ℝ)^6339 := by
    have hnat : (259141873 : ℕ)^8387*50000000000000^6339 ≤ 6234678559757^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259141873 1250000000 6234678559757 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699554933/5000000000 : ℝ)^8387 ≤ (44242634925477/100000000000000 : ℝ)^6339 := by
    have hnat : (2699554933 : ℕ)^8387*100000000000000^6339 ≤ 44242634925477^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699554933 5000000000 44242634925477 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655412939/5000000000 : ℝ), (-259141873/1250000000 : ℝ), (2699554933/5000000000 : ℝ)] ![(43288007945561/100000000000000 : ℝ), (6234678559757/50000000000000 : ℝ), (44242634925477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655412939/5000000000 : ℝ)|^8387 ≤ (43288007945561/100000000000000 : ℝ)^6339
        have hw : |(2655412939/5000000000 : ℝ)|=(2655412939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259141873/1250000000 : ℝ)|^8387 ≤ (6234678559757/50000000000000 : ℝ)^6339
        have hw : |(-259141873/1250000000 : ℝ)|=(259141873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699554933/5000000000 : ℝ)|^8387 ≤ (44242634925477/100000000000000 : ℝ)^6339
        have hw : |(2699554933/5000000000 : ℝ)|=(2699554933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s4_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327706277/2500000000 : ℝ)*x 0 + (33744443/62500000 : ℝ)*x 1 + (-414626929/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327706277/2500000000 : ℝ)^8387 ≤ (2164399982083/5000000000000 : ℝ)^6339 := by
    have hnat : (1327706277 : ℕ)^8387*5000000000000^6339 ≤ 2164399982083^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327706277 2500000000 2164399982083 5000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33744443/62500000 : ℝ)^8387 ≤ (44242645919147/100000000000000 : ℝ)^6339 := by
    have hnat : (33744443 : ℕ)^8387*100000000000000^6339 ≤ 44242645919147^6339*62500000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33744443 62500000 44242645919147 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414626929/2000000000 : ℝ)^8387 ≤ (6234677210881/50000000000000 : ℝ)^6339 := by
    have hnat : (414626929 : ℕ)^8387*50000000000000^6339 ≤ 6234677210881^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414626929 2000000000 6234677210881 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327706277/2500000000 : ℝ), (33744443/62500000 : ℝ), (-414626929/2000000000 : ℝ)] ![(2164399982083/5000000000000 : ℝ), (44242645919147/100000000000000 : ℝ), (6234677210881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327706277/2500000000 : ℝ)|^8387 ≤ (2164399982083/5000000000000 : ℝ)^6339
        have hw : |(1327706277/2500000000 : ℝ)|=(1327706277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33744443/62500000 : ℝ)|^8387 ≤ (44242645919147/100000000000000 : ℝ)^6339
        have hw : |(33744443/62500000 : ℝ)|=(33744443/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414626929/2000000000 : ℝ)|^8387 ≤ (6234677210881/50000000000000 : ℝ)^6339
        have hw : |(-414626929/2000000000 : ℝ)|=(414626929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s4_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357026477/10000000000 : ℝ)*x 0 + (4499088293/10000000000 : ℝ)*x 1 + (527425267/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357026477/10000000000 : ℝ)^8387 ≤ (16656740026397/50000000000000 : ℝ)^6339 := by
    have hnat : (4357026477 : ℕ)^8387*50000000000000^6339 ≤ 16656740026397^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357026477 10000000000 16656740026397 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499088293/10000000000 : ℝ)^8387 ≤ (17379057278273/50000000000000 : ℝ)^6339 := by
    have hnat : (4499088293 : ℕ)^8387*50000000000000^6339 ≤ 17379057278273^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499088293 10000000000 17379057278273 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527425267/1250000000 : ℝ)^8387 ≤ (31928405367651/100000000000000 : ℝ)^6339 := by
    have hnat : (527425267 : ℕ)^8387*100000000000000^6339 ≤ 31928405367651^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527425267 1250000000 31928405367651 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357026477/10000000000 : ℝ), (4499088293/10000000000 : ℝ), (527425267/1250000000 : ℝ)] ![(16656740026397/50000000000000 : ℝ), (17379057278273/50000000000000 : ℝ), (31928405367651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357026477/10000000000 : ℝ)|^8387 ≤ (16656740026397/50000000000000 : ℝ)^6339
        have hw : |(4357026477/10000000000 : ℝ)|=(4357026477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499088293/10000000000 : ℝ)|^8387 ≤ (17379057278273/50000000000000 : ℝ)^6339
        have hw : |(4499088293/10000000000 : ℝ)|=(4499088293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527425267/1250000000 : ℝ)|^8387 ≤ (31928405367651/100000000000000 : ℝ)^6339
        have hw : |(527425267/1250000000 : ℝ)|=(527425267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (337/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11271/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (337/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (337/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (337/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (337/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (337/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (337/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (337/3125 : ℝ) ^ (4193/1024 : ℝ) ≤ (68450732019059/625000000000000000 : ℝ) := by
    have hpowers : (337/3125 : ℝ)^4193 ≤ (68450732019059/625000000000000000 : ℝ)^1024 := by
      have hnat : (337 : ℕ)^4193*625000000000000000^1024 ≤ 68450732019059^1024*3125^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        337 3125 68450732019059 625000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (337/3125 : ℝ)) (X := (68450732019059/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (4193/1024 : ℝ) ≤ (986299667873733/2500000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^4193 ≤ (986299667873733/2500000000000000000 : ℝ)^1024 := by
      have hnat : (14747 : ℕ)^4193*2500000000000000000^1024 ≤ 986299667873733^1024*100000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 986299667873733 2500000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (986299667873733/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312568450732019059/312500000000000000 : ℝ) ≤ (5000267446690723/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (312568450732019059/312500000000000000 : ℝ)^1024 ≤ (5000267446690723/5000000000000000 : ℝ)^4193 := by
      have hnat : (312568450732019059 : ℕ)^1024*5000000000000000^4193 ≤ 5000267446690723^4193*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312568450732019059 312500000000000000 5000267446690723 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000267446690723/5000000000000000 : ℝ)) (X := (312568450732019059/312500000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501260102595949969/2500000000000000000 : ℝ) ≤ (2500307679311929/2500000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (2501260102595949969/2500000000000000000 : ℝ)^1024 ≤ (2500307679311929/2500000000000000 : ℝ)^4193 := by
      have hnat : (2501260102595949969 : ℕ)^1024*2500000000000000^4193 ≤ 2500307679311929^4193*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501260102595949969 2500000000000000000 2500307679311929 2500000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500307679311929/2500000000000000 : ℝ)) (X := (2501260102595949969/2500000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250986299667873733/1250000000000000000 : ℝ) ≤ (5000963270556993/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (1250986299667873733/1250000000000000000 : ℝ)^1024 ≤ (5000963270556993/5000000000000000 : ℝ)^4193 := by
      have hnat : (1250986299667873733 : ℕ)^1024*5000000000000000^4193 ≤ 5000963270556993^4193*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250986299667873733 1250000000000000000 5000963270556993 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000963270556993/5000000000000000 : ℝ)) (X := (1250986299667873733/1250000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(68450732019059/625000000000000000 : ℝ) ≤ ((19808556126661479569/19815000000000000000 : ℝ)+2*(69582386627/39630000000000 : ℝ)*(337/3125 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (19808556126661479569/19815000000000000000 : ℝ)+2*(69582386627/39630000000000 : ℝ)*(337/3125 : ℝ)=(5000267446690723/5000000000000000 : ℝ) by norm_num, show 1+2*(68450732019059/625000000000000000 : ℝ)=(312568450732019059/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(986299667873733/2500000000000000000 : ℝ)+(68450732019059/625000000000000000 : ℝ) ≤ ((19808556126661479569/19815000000000000000 : ℝ)+(69582386627/39630000000000 : ℝ)*((14747/100000 : ℝ)+(337/3125 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (19808556126661479569/19815000000000000000 : ℝ)+(69582386627/39630000000000 : ℝ)*((14747/100000 : ℝ)+(337/3125 : ℝ))=(2500307679311929/2500000000000000 : ℝ) by norm_num, show 1+(986299667873733/2500000000000000000 : ℝ)+(68450732019059/625000000000000000 : ℝ)=(2501260102595949969/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(986299667873733/2500000000000000000 : ℝ) ≤ ((19808556126661479569/19815000000000000000 : ℝ)+2*(69582386627/39630000000000 : ℝ)*(14747/100000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (19808556126661479569/19815000000000000000 : ℝ)+2*(69582386627/39630000000000 : ℝ)*(14747/100000 : ℝ)=(5000963270556993/5000000000000000 : ℝ) by norm_num, show 1+2*(986299667873733/2500000000000000000 : ℝ)=(1250986299667873733/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19808556126661479569/19815000000000000000 : ℝ)*(X 1 0+X 2 0)+(69582386627/39630000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (337/3125 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (19808556126661479569/19815000000000000000 : ℝ)) (alpha := (69582386627/39630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19808556126661479569/19815000000000000000 : ℝ)*(X 0 1+X 2 1)+(69582386627/39630000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (337/3125 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (19808556126661479569/19815000000000000000 : ℝ)) (alpha := (69582386627/39630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19808556126661479569/19815000000000000000 : ℝ)*(X 0 2+X 1 2)+(69582386627/39630000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (337/3125 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (19808556126661479569/19815000000000000000 : ℝ)) (alpha := (69582386627/39630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1070802471/5000000000 : ℝ)*X 0 0+(5399504273/10000000000 : ℝ)*X 0 1+(5259556103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673207039/5000000000 : ℝ)*X 1 0+(-1106344311/5000000000 : ℝ)*X 1 1+(5259556179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346413969/10000000000 : ℝ)*X 2 0+(5259556073/10000000000 : ℝ)*X 2 1+(-553172227/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357013073/10000000000 : ℝ)*X 0 0+(4218610507/10000000000 : ℝ)*X 0 1+(4499876897/10000000000 : ℝ)*X 0 2+(4357013073/10000000000 : ℝ)*X 1 0+(4218610507/10000000000 : ℝ)*X 1 1+(4499876897/10000000000 : ℝ)*X 1 2+(4357013073/10000000000 : ℝ)*X 2 0+(4218610507/10000000000 : ℝ)*X 2 1+(4499876897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214161163/1000000000 : ℝ)*X 0 0+(5259948677/10000000000 : ℝ)*X 0 1+(1079822009/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655412939/5000000000 : ℝ)*X 1 0+(-259141873/1250000000 : ℝ)*X 1 1+(2699554933/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327706277/2500000000 : ℝ)*X 2 0+(33744443/62500000 : ℝ)*X 2 1+(-414626929/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357026477/10000000000 : ℝ)*X 0 0+(4499088293/10000000000 : ℝ)*X 0 1+(527425267/1250000000 : ℝ)*X 0 2+(4357026477/10000000000 : ℝ)*X 1 0+(4499088293/10000000000 : ℝ)*X 1 1+(527425267/1250000000 : ℝ)*X 1 2+(4357026477/10000000000 : ℝ)*X 2 0+(4499088293/10000000000 : ℝ)*X 2 1+(527425267/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1145541401527950687819/1321000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582876709/100000000000000 : ℝ)*(base19) + (302225031/50000000000000 : ℝ)*(base23) + (53423903/50000000000000 : ℝ)*(upper2) + (33825269/20000000000000 : ℝ)*(upper3) + (5350455244548559/100000000000000 : ℝ)*(major0) + (5350455244548559/100000000000000 : ℝ)*(major1) + (5350455244548559/100000000000000 : ℝ)*(major2) + (893190787914523/12500000000000 : ℝ)*(sp0) + (223298040382801/3125000000000 : ℝ)*(sp1) + (357276618689771/5000000000000 : ℝ)*(sp2) + (888839941511327/25000000000000 : ℝ)*(sp3) + (11571810157/100000000000000 : ℝ)*(sp4) + (4896880859/100000000000000 : ℝ)*(sp6) + (12819019551/100000000000000 : ℝ)*(sp7) + (3555372585064859/100000000000000 : ℝ)*(f.failure) + (7145537875126341/100000000000000 : ℝ)*(f.sum) + (6140326423687/3963000000000000000000000000 : ℝ)*base65 + (4674332864708869643/660500000000000000000000000000000 : ℝ)*base68 + (1327977986296630357/660500000000000000000000000000000 : ℝ)*base69 + (970069959627630357/660500000000000000000000000000000 : ℝ)*base71 + (6253967739301/3963000000000000000000000000 : ℝ)*base73 + (2247078193981130357/660500000000000000000000000000000 : ℝ)*base75 + (3708192396560369643/660500000000000000000000000000000 : ℝ)*base78 + (1917316736178369643/660500000000000000000000000000000 : ℝ)*base80 + (850130230339/158520000000000000000000000 : ℝ)*base81 + (7689491/5000000000000000000000 : ℝ)*base89 + (7689491/5000000000000000000000 : ℝ)*base91 + (7689491/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20401324166318778553987859/6605000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93079079/10000000000000 : ℝ)*(base19) + (48038521/100000000000000 : ℝ)*(upper2) + (299619281/100000000000000 : ℝ)*(upper3) + (56995127/100000000000000 : ℝ)*(upper4) + (87908089/100000000000000 : ℝ)*(upper5) + (107613325880411/2000000000000 : ℝ)*(major0) + (107613325880411/2000000000000 : ℝ)*(major1) + (107613325880411/2000000000000 : ℝ)*(major2) + (3818213871/20000000000000 : ℝ)*(sp2) + (5874652007/100000000000000 : ℝ)*(sp3) + (449117792840717/6250000000000 : ℝ)*(sp4) + (3592941877330341/50000000000000 : ℝ)*(sp5) + (3592932797191059/50000000000000 : ℝ)*(sp6) + (1787720962489301/50000000000000 : ℝ)*(sp7) + (223465487476913/6250000000000 : ℝ)*(f.failure) + (449117792840717/6250000000000 : ℝ)*(f.sum) + (62208103651603/792600000000000000000000000 : ℝ)*base66 + (118938943100149047/13210000000000000000000000000000 : ℝ)*base68 + (112728471797669047/13210000000000000000000000000000 : ℝ)*base70 + (164354592987630953/13210000000000000000000000000000 : ℝ)*base71 + (14480238358961/3963000000000000000000000000 : ℝ)*base74 + (31265735631789047/13210000000000000000000000000000 : ℝ)*base76 + (617910564640600953/13210000000000000000000000000000 : ℝ)*base77 + (185406170527459047/13210000000000000000000000000000 : ℝ)*base80 + (72481698162637/3963000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4461463/312500000000000000000 : ℝ)*base90 + (4461463/312500000000000000000 : ℝ)*base92 + (4461463/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1194_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (337/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1194_s5_0 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-535533779/2500000000 : ℝ)*x 0 + (5393578261/10000000000 : ℝ)*x 1 + (2632566989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535533779/2500000000 : ℝ)^8387 ≤ (13021388584053/100000000000000 : ℝ)^6339 := by
    have hnat : (535533779 : ℕ)^8387*100000000000000^6339 ≤ 13021388584053^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535533779 2500000000 13021388584053 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393578261/10000000000 : ℝ)^8387 ≤ (44182671840157/100000000000000 : ℝ)^6339 := by
    have hnat : (5393578261 : ℕ)^8387*100000000000000^6339 ≤ 44182671840157^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393578261 10000000000 44182671840157 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632566989/5000000000 : ℝ)^8387 ≤ (2674746222653/6250000000000 : ℝ)^6339 := by
    have hnat : (2632566989 : ℕ)^8387*6250000000000^6339 ≤ 2674746222653^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632566989 5000000000 2674746222653 6250000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535533779/2500000000 : ℝ), (5393578261/10000000000 : ℝ), (2632566989/5000000000 : ℝ)] ![(13021388584053/100000000000000 : ℝ), (44182671840157/100000000000000 : ℝ), (2674746222653/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535533779/2500000000 : ℝ)|^8387 ≤ (13021388584053/100000000000000 : ℝ)^6339
        have hw : |(-535533779/2500000000 : ℝ)|=(535533779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393578261/10000000000 : ℝ)|^8387 ≤ (44182671840157/100000000000000 : ℝ)^6339
        have hw : |(5393578261/10000000000 : ℝ)|=(5393578261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632566989/5000000000 : ℝ)|^8387 ≤ (2674746222653/6250000000000 : ℝ)^6339
        have hw : |(2632566989/5000000000 : ℝ)|=(2632566989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s5_1 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336230267/2500000000 : ℝ)*x 0 + (-551823087/2500000000 : ℝ)*x 1 + (263256699/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336230267/2500000000 : ℝ)^8387 ≤ (43656081026727/100000000000000 : ℝ)^6339 := by
    have hnat : (1336230267 : ℕ)^8387*100000000000000^6339 ≤ 43656081026727^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336230267 2500000000 43656081026727 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551823087/2500000000 : ℝ)^8387 ≤ (3386994845297/25000000000000 : ℝ)^6339 := by
    have hnat : (551823087 : ℕ)^8387*25000000000000^6339 ≤ 3386994845297^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551823087 2500000000 3386994845297 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263256699/500000000 : ℝ)^8387 ≤ (10698984895989/25000000000000 : ℝ)^6339 := by
    have hnat : (263256699 : ℕ)^8387*25000000000000^6339 ≤ 10698984895989^6339*500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263256699 500000000 10698984895989 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336230267/2500000000 : ℝ), (-551823087/2500000000 : ℝ), (263256699/500000000 : ℝ)] ![(43656081026727/100000000000000 : ℝ), (3386994845297/25000000000000 : ℝ), (10698984895989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336230267/2500000000 : ℝ)|^8387 ≤ (43656081026727/100000000000000 : ℝ)^6339
        have hw : |(1336230267/2500000000 : ℝ)|=(1336230267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551823087/2500000000 : ℝ)|^8387 ≤ (3386994845297/25000000000000 : ℝ)^6339
        have hw : |(-551823087/2500000000 : ℝ)|=(551823087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263256699/500000000 : ℝ)|^8387 ≤ (10698984895989/25000000000000 : ℝ)^6339
        have hw : |(263256699/500000000 : ℝ)|=(263256699/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s5_2 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068984203/2000000000 : ℝ)*x 0 + (1316283501/2500000000 : ℝ)*x 1 + (-1103646193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068984203/2000000000 : ℝ)^8387 ≤ (43656080453977/100000000000000 : ℝ)^6339 := by
    have hnat : (1068984203 : ℕ)^8387*100000000000000^6339 ≤ 43656080453977^6339*2000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068984203 2000000000 43656080453977 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316283501/2500000000 : ℝ)^8387 ≤ (21397969921029/50000000000000 : ℝ)^6339 := by
    have hnat : (1316283501 : ℕ)^8387*50000000000000^6339 ≤ 21397969921029^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316283501 2500000000 21397969921029 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103646193/5000000000 : ℝ)^8387 ≤ (677398984489/5000000000000 : ℝ)^6339 := by
    have hnat : (1103646193 : ℕ)^8387*5000000000000^6339 ≤ 677398984489^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103646193 5000000000 677398984489 5000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068984203/2000000000 : ℝ), (1316283501/2500000000 : ℝ), (-1103646193/5000000000 : ℝ)] ![(43656080453977/100000000000000 : ℝ), (21397969921029/50000000000000 : ℝ), (677398984489/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068984203/2000000000 : ℝ)|^8387 ≤ (43656080453977/100000000000000 : ℝ)^6339
        have hw : |(1068984203/2000000000 : ℝ)|=(1068984203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316283501/2500000000 : ℝ)|^8387 ≤ (21397969921029/50000000000000 : ℝ)^6339
        have hw : |(1316283501/2500000000 : ℝ)|=(1316283501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103646193/5000000000 : ℝ)|^8387 ≤ (677398984489/5000000000000 : ℝ)^6339
        have hw : |(-1103646193/5000000000 : ℝ)|=(1103646193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s5_3 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357324331/10000000000 : ℝ)*x 0 + (84602619/200000000 : ℝ)*x 1 + (4488276359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357324331/10000000000 : ℝ)^8387 ≤ (8329123306207/25000000000000 : ℝ)^6339 := by
    have hnat : (4357324331 : ℕ)^8387*25000000000000^6339 ≤ 8329123306207^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357324331 10000000000 8329123306207 25000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84602619/200000000 : ℝ)^8387 ≤ (32035864212167/100000000000000 : ℝ)^6339 := by
    have hnat : (84602619 : ℕ)^8387*100000000000000^6339 ≤ 32035864212167^6339*200000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84602619 200000000 32035864212167 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488276359/10000000000 : ℝ)^8387 ≤ (34647642547309/100000000000000 : ℝ)^6339 := by
    have hnat : (4488276359 : ℕ)^8387*100000000000000^6339 ≤ 34647642547309^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488276359 10000000000 34647642547309 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357324331/10000000000 : ℝ), (84602619/200000000 : ℝ), (4488276359/10000000000 : ℝ)] ![(8329123306207/25000000000000 : ℝ), (32035864212167/100000000000000 : ℝ), (34647642547309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357324331/10000000000 : ℝ)|^8387 ≤ (8329123306207/25000000000000 : ℝ)^6339
        have hw : |(4357324331/10000000000 : ℝ)|=(4357324331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84602619/200000000 : ℝ)|^8387 ≤ (32035864212167/100000000000000 : ℝ)^6339
        have hw : |(84602619/200000000 : ℝ)|=(84602619/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488276359/10000000000 : ℝ)|^8387 ≤ (34647642547309/100000000000000 : ℝ)^6339
        have hw : |(4488276359/10000000000 : ℝ)|=(4488276359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s5_4 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-10710701/50000000 : ℝ)*x 0 + (5265464781/10000000000 : ℝ)*x 1 + (1348311561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10710701/50000000 : ℝ)^8387 ≤ (6510714736317/50000000000000 : ℝ)^6339 := by
    have hnat : (10710701 : ℕ)^8387*50000000000000^6339 ≤ 6510714736317^6339*50000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10710701 50000000 6510714736317 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265464781/10000000000 : ℝ)^8387 ≤ (42799497127721/100000000000000 : ℝ)^6339 := by
    have hnat : (5265464781 : ℕ)^8387*100000000000000^6339 ≤ 42799497127721^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265464781 10000000000 42799497127721 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348311561/2500000000 : ℝ)^8387 ≤ (44179073378461/100000000000000 : ℝ)^6339 := by
    have hnat : (1348311561 : ℕ)^8387*100000000000000^6339 ≤ 44179073378461^6339*2500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348311561 2500000000 44179073378461 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10710701/50000000 : ℝ), (5265464781/10000000000 : ℝ), (1348311561/2500000000 : ℝ)] ![(6510714736317/50000000000000 : ℝ), (42799497127721/100000000000000 : ℝ), (44179073378461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10710701/50000000 : ℝ)|^8387 ≤ (6510714736317/50000000000000 : ℝ)^6339
        have hw : |(-10710701/50000000 : ℝ)|=(10710701/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265464781/10000000000 : ℝ)|^8387 ≤ (42799497127721/100000000000000 : ℝ)^6339
        have hw : |(5265464781/10000000000 : ℝ)|=(5265464781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348311561/2500000000 : ℝ)|^8387 ≤ (44179073378461/100000000000000 : ℝ)^6339
        have hw : |(1348311561/2500000000 : ℝ)|=(1348311561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s5_5 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531225687/1000000000 : ℝ)*x 0 + (-1039590037/5000000000 : ℝ)*x 1 + (674155773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531225687/1000000000 : ℝ)^8387 ≤ (4330344084537/10000000000000 : ℝ)^6339 := by
    have hnat : (531225687 : ℕ)^8387*10000000000000^6339 ≤ 4330344084537^6339*1000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531225687 1000000000 4330344084537 10000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039590037/5000000000 : ℝ)^8387 ≤ (12517486417941/100000000000000 : ℝ)^6339 := by
    have hnat : (1039590037 : ℕ)^8387*100000000000000^6339 ≤ 12517486417941^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039590037 5000000000 12517486417941 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674155773/1250000000 : ℝ)^8387 ≤ (44179072728177/100000000000000 : ℝ)^6339 := by
    have hnat : (674155773 : ℕ)^8387*100000000000000^6339 ≤ 44179072728177^6339*1250000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674155773 1250000000 44179072728177 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531225687/1000000000 : ℝ), (-1039590037/5000000000 : ℝ), (674155773/1250000000 : ℝ)] ![(4330344084537/10000000000000 : ℝ), (12517486417941/100000000000000 : ℝ), (44179072728177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531225687/1000000000 : ℝ)|^8387 ≤ (4330344084537/10000000000000 : ℝ)^6339
        have hw : |(531225687/1000000000 : ℝ)|=(531225687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039590037/5000000000 : ℝ)|^8387 ≤ (12517486417941/100000000000000 : ℝ)^6339
        have hw : |(-1039590037/5000000000 : ℝ)|=(1039590037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674155773/1250000000 : ℝ)|^8387 ≤ (44179072728177/100000000000000 : ℝ)^6339
        have hw : |(674155773/1250000000 : ℝ)|=(674155773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s5_6 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312256927/10000000000 : ℝ)*x 0 + (2696623069/5000000000 : ℝ)*x 1 + (-103959003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312256927/10000000000 : ℝ)^8387 ≤ (1353232545629/3125000000000 : ℝ)^6339 := by
    have hnat : (5312256927 : ℕ)^8387*3125000000000^6339 ≤ 1353232545629^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312256927 10000000000 1353232545629 3125000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696623069/5000000000 : ℝ)^8387 ≤ (353432577837/800000000000 : ℝ)^6339 := by
    have hnat : (2696623069 : ℕ)^8387*800000000000^6339 ≤ 353432577837^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696623069 5000000000 353432577837 800000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103959003/500000000 : ℝ)^8387 ≤ (500699452257/4000000000000 : ℝ)^6339 := by
    have hnat : (103959003 : ℕ)^8387*4000000000000^6339 ≤ 500699452257^6339*500000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103959003 500000000 500699452257 4000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312256927/10000000000 : ℝ), (2696623069/5000000000 : ℝ), (-103959003/500000000 : ℝ)] ![(1353232545629/3125000000000 : ℝ), (353432577837/800000000000 : ℝ), (500699452257/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312256927/10000000000 : ℝ)|^8387 ≤ (1353232545629/3125000000000 : ℝ)^6339
        have hw : |(5312256927/10000000000 : ℝ)|=(5312256927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696623069/5000000000 : ℝ)|^8387 ≤ (353432577837/800000000000 : ℝ)^6339
        have hw : |(2696623069/5000000000 : ℝ)|=(2696623069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103959003/500000000 : ℝ)|^8387 ≤ (500699452257/4000000000000 : ℝ)^6339
        have hw : |(-103959003/500000000 : ℝ)|=(103959003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1194_s5_7 (p : ℝ) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357334609/10000000000 : ℝ)*x 0 + (2243805871/5000000000 : ℝ)*x 1 + (4230797999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357334609/10000000000 : ℝ)^8387 ≤ (16658298600529/50000000000000 : ℝ)^6339 := by
    have hnat : (4357334609 : ℕ)^8387*50000000000000^6339 ≤ 16658298600529^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357334609 10000000000 16658298600529 50000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243805871/5000000000 : ℝ)^8387 ≤ (34640854559587/100000000000000 : ℝ)^6339 := by
    have hnat : (2243805871 : ℕ)^8387*100000000000000^6339 ≤ 34640854559587^6339*5000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243805871 5000000000 34640854559587 100000000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230797999/10000000000 : ℝ)^8387 ≤ (2002659264109/6250000000000 : ℝ)^6339 := by
    have hnat : (4230797999 : ℕ)^8387*6250000000000^6339 ≤ 2002659264109^6339*10000000000^8387 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230797999 10000000000 2002659264109 6250000000000 8387 6339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8387/2048 : ℝ)) 8387 6339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357334609/10000000000 : ℝ), (2243805871/5000000000 : ℝ), (4230797999/10000000000 : ℝ)] ![(16658298600529/50000000000000 : ℝ), (34640854559587/100000000000000 : ℝ), (2002659264109/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357334609/10000000000 : ℝ)|^8387 ≤ (16658298600529/50000000000000 : ℝ)^6339
        have hw : |(4357334609/10000000000 : ℝ)|=(4357334609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243805871/5000000000 : ℝ)|^8387 ≤ (34640854559587/100000000000000 : ℝ)^6339
        have hw : |(2243805871/5000000000 : ℝ)|=(2243805871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230797999/10000000000 : ℝ)|^8387 ≤ (2002659264109/6250000000000 : ℝ)^6339
        have hw : |(4230797999/10000000000 : ℝ)|=(4230797999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1194_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11271/100000 : ℝ) ^ (4193/1024 : ℝ) ≤ (13123372640696813/100000000000000000000 : ℝ) := by
    have hpowers : (11271/100000 : ℝ)^4193 ≤ (13123372640696813/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11271 : ℕ)^4193*100000000000000000000^1024 ≤ 13123372640696813^1024*100000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11271 100000 13123372640696813 100000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11271/100000 : ℝ)) (X := (13123372640696813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4193/1024 : ℝ) ≤ (3412757419161809/10000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4193 ≤ (3412757419161809/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4193*10000000000000000000^1024 ≤ 3412757419161809^1024*50000^4193 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 3412757419161809 10000000000000000000 4193 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (3412757419161809/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013123372640696813/50000000000000000000 : ℝ) ≤ (5000320462697767/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (50013123372640696813/50000000000000000000 : ℝ)^1024 ≤ (5000320462697767/5000000000000000 : ℝ)^4193 := by
      have hnat : (50013123372640696813 : ℕ)^1024*5000000000000000^4193 ≤ 5000320462697767^4193*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013123372640696813 50000000000000000000 5000320462697767 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000320462697767/5000000000000000 : ℝ)) (X := (50013123372640696813/50000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047250946832314903/100000000000000000000 : ℝ) ≤ (15626802719281/15625000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (100047250946832314903/100000000000000000000 : ℝ)^1024 ≤ (15626802719281/15625000000000 : ℝ)^4193 := by
      have hnat : (100047250946832314903 : ℕ)^1024*15625000000000^4193 ≤ 15626802719281^4193*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047250946832314903 100000000000000000000 15626802719281 15625000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15626802719281/15625000000000 : ℝ)) (X := (100047250946832314903/100000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003412757419161809/5000000000000000000 : ℝ) ≤ (5000833277642073/5000000000000000 : ℝ) ^ (4193/1024 : ℝ) := by
    have hpowers : (5003412757419161809/5000000000000000000 : ℝ)^1024 ≤ (5000833277642073/5000000000000000 : ℝ)^4193 := by
      have hnat : (5003412757419161809 : ℕ)^1024*5000000000000000^4193 ≤ 5000833277642073^4193*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003412757419161809 5000000000000000000 5000833277642073 5000000000000000 1024 4193 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000833277642073/5000000000000000 : ℝ)) (X := (5003412757419161809/5000000000000000000 : ℝ)) (by norm_num) 4193 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13123372640696813/100000000000000000000 : ℝ) ≤ ((2962033918747242139/2963000000000000000 : ℝ)+2*(256407472153/148150000000000 : ℝ)*(11271/100000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (2962033918747242139/2963000000000000000 : ℝ)+2*(256407472153/148150000000000 : ℝ)*(11271/100000 : ℝ)=(5000320462697767/5000000000000000 : ℝ) by norm_num, show 1+2*(13123372640696813/100000000000000000000 : ℝ)=(50013123372640696813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3412757419161809/10000000000000000000 : ℝ)+(13123372640696813/100000000000000000000 : ℝ) ≤ ((2962033918747242139/2963000000000000000 : ℝ)+(256407472153/148150000000000 : ℝ)*((7117/50000 : ℝ)+(11271/100000 : ℝ)))^(4193/1024 : ℝ) := by
    rw [show (2962033918747242139/2963000000000000000 : ℝ)+(256407472153/148150000000000 : ℝ)*((7117/50000 : ℝ)+(11271/100000 : ℝ))=(15626802719281/15625000000000 : ℝ) by norm_num, show 1+(3412757419161809/10000000000000000000 : ℝ)+(13123372640696813/100000000000000000000 : ℝ)=(100047250946832314903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3412757419161809/10000000000000000000 : ℝ) ≤ ((2962033918747242139/2963000000000000000 : ℝ)+2*(256407472153/148150000000000 : ℝ)*(7117/50000 : ℝ))^(4193/1024 : ℝ) := by
    rw [show (2962033918747242139/2963000000000000000 : ℝ)+2*(256407472153/148150000000000 : ℝ)*(7117/50000 : ℝ)=(5000833277642073/5000000000000000 : ℝ) by norm_num, show 1+2*(3412757419161809/10000000000000000000 : ℝ)=(5003412757419161809/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2962033918747242139/2963000000000000000 : ℝ)*(X 1 0+X 2 0)+(256407472153/148150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (2962033918747242139/2963000000000000000 : ℝ)) (alpha := (256407472153/148150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2962033918747242139/2963000000000000000 : ℝ)*(X 0 1+X 2 1)+(256407472153/148150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (2962033918747242139/2963000000000000000 : ℝ)) (alpha := (256407472153/148150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2962033918747242139/2963000000000000000 : ℝ)*(X 0 2+X 1 2)+(256407472153/148150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4193/1024 : ℝ)) (lo := (11271/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (2962033918747242139/2963000000000000000 : ℝ)) (alpha := (256407472153/148150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-535533779/2500000000 : ℝ)*X 0 0+(5393578261/10000000000 : ℝ)*X 0 1+(2632566989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336230267/2500000000 : ℝ)*X 1 0+(-551823087/2500000000 : ℝ)*X 1 1+(263256699/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068984203/2000000000 : ℝ)*X 2 0+(1316283501/2500000000 : ℝ)*X 2 1+(-1103646193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357324331/10000000000 : ℝ)*X 0 0+(84602619/200000000 : ℝ)*X 0 1+(4488276359/10000000000 : ℝ)*X 0 2+(4357324331/10000000000 : ℝ)*X 1 0+(84602619/200000000 : ℝ)*X 1 1+(4488276359/10000000000 : ℝ)*X 1 2+(4357324331/10000000000 : ℝ)*X 2 0+(84602619/200000000 : ℝ)*X 2 1+(4488276359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-10710701/50000000 : ℝ)*X 0 0+(5265464781/10000000000 : ℝ)*X 0 1+(1348311561/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531225687/1000000000 : ℝ)*X 1 0+(-1039590037/5000000000 : ℝ)*X 1 1+(674155773/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312256927/10000000000 : ℝ)*X 2 0+(2696623069/5000000000 : ℝ)*X 2 1+(-103959003/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357334609/10000000000 : ℝ)*X 0 0+(2243805871/5000000000 : ℝ)*X 0 1+(4230797999/10000000000 : ℝ)*X 0 2+(4357334609/10000000000 : ℝ)*X 1 0+(2243805871/5000000000 : ℝ)*X 1 1+(4230797999/10000000000 : ℝ)*X 1 2+(4357334609/10000000000 : ℝ)*X 2 0+(2243805871/5000000000 : ℝ)*X 2 1+(4230797999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1194_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1541154014622513104418099081/148150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1906758243/100000000000000 : ℝ)*(base19) + (419396727/25000000000000 : ℝ)*(base23) + (81226703/100000000000000 : ℝ)*(lower2) + (735191/250000000000 : ℝ)*(upper3) + (106543909/100000000000000 : ℝ)*(upper5) + (5829707624321993/100000000000000 : ℝ)*(major0) + (5829707624321993/100000000000000 : ℝ)*(major1) + (5829707624321993/100000000000000 : ℝ)*(major2) + (1557106382658223/20000000000000 : ℝ)*(sp0) + (1946394411210979/25000000000000 : ℝ)*(sp1) + (31142311496061/400000000000 : ℝ)*(sp2) + (774761677581747/20000000000000 : ℝ)*(sp3) + (11909577761/25000000000000 : ℝ)*(sp4) + (5392475553/20000000000000 : ℝ)*(sp7) + (3873835350286499/100000000000000 : ℝ)*(f.failure) + (7785579551602159/100000000000000 : ℝ)*(f.sum) + (13307811834699/1851875000000000000000000000 : ℝ)*base66 + (1353775238149056973/296300000000000000000000000000000 : ℝ)*base68 + (2063311528575156973/296300000000000000000000000000000 : ℝ)*base70 + (3650179103387243027/296300000000000000000000000000000 : ℝ)*base71 + (32124117443711/7407500000000000000000000000 : ℝ)*base74 + (871931147321356973/296300000000000000000000000000000 : ℝ)*base76 + (6410822646303356973/296300000000000000000000000000000 : ℝ)*base78 + (2363080519448643027/296300000000000000000000000000000 : ℝ)*base79 + (1826638641071/7407500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16693851/5000000000000000000000 : ℝ)*base89 + (16693851/5000000000000000000000 : ℝ)*base91 + (16693851/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27654526605187670674455039/5926000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61300467/6250000000000 : ℝ)*(base19) + (1242937091/100000000000000 : ℝ)*(base23) + (7111323/5000000000000 : ℝ)*(upper3) + (12752271/20000000000000 : ℝ)*(lower4) + (26548367/100000000000000 : ℝ)*(upper5) + (234394602964789/4000000000000 : ℝ)*(major0) + (234394602964789/4000000000000 : ℝ)*(major1) + (234394602964789/4000000000000 : ℝ)*(major2) + (5125434161/25000000000000 : ℝ)*(sp1) + (5991200101/20000000000000 : ℝ)*(sp2) + (3912927522383317/50000000000000 : ℝ)*(sp4) + (3912916781111259/50000000000000 : ℝ)*(sp5) + (3912911922914519/50000000000000 : ℝ)*(sp6) + (3893874947918041/100000000000000 : ℝ)*(sp7) + (3893874947918041/100000000000000 : ℝ)*(f.failure) + (3912927522383317/50000000000000 : ℝ)*(f.sum) + (2224171384423/2963000000000000000000000000 : ℝ)*base65 + (106273668946368329/11852000000000000000000000000000 : ℝ)*base68 + (101726863418676329/11852000000000000000000000000000 : ℝ)*base70 + (219934833041308329/11852000000000000000000000000000 : ℝ)*base72 + (986835779839/740750000000000000000000000 : ℝ)*base73 + (35603509313748329/11852000000000000000000000000000 : ℝ)*base76 + (206671785465656329/11852000000000000000000000000000 : ℝ)*base78 + (101858918770088329/11852000000000000000000000000000 : ℝ)*base80 + (1233260218117/2963000000000000000000000000 : ℝ)*base82 + (25812609/5000000000000000000000 : ℝ)*base89 + (25812609/5000000000000000000000 : ℝ)*base91 + (25812609/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1194_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1194_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1194_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1194_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1194_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1194_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4193/1024 : ℝ) ≤ p) (hpb : p ≤ (8387/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75244649/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1194_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
